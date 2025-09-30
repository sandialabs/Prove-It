"""
A Judgment represents an expression that has been proven to be a true
statement.  A Judgment wraps an Expression (acting like the Expression
in many ways via overloading __getattr__) but also has a list of assumptions
and its proof (as a Proof object, which may be updated if a newer proof,
with possibly fewer assumptions, suffices).
"""

from functools import wraps
from proveit._core_.expression import Expression
from proveit._core_._unique_data import meaning_data, style_data
from proveit.decorators import prover
from .defaults import defaults, USE_DEFAULTS
import re
from copy import copy
from inspect import signature, Parameter
from proveit.util import OrderedSet


class _ExprProofs:
    '''
    Stores a set of proofs for a particular expression under any set
    of assumptions.  We maintain such sets so that we can update
    Judgment proofs appropriately when a particular proof has been
    disabled.
    '''
    all_expr_proofs = dict()  # map expressions to expression proofs

    def __init__(self, expr, num_lit_gen):
        self._expr = expr
        self._proofs = set()
        _ExprProofs.all_expr_proofs[(expr, num_lit_gen)] = self

    def insert(self, newproof):
        '''
        Insert a new proof for the expression, maintaining sorted order
        in the proof size (number of steps).
        '''
        from .proof import Proof
        assert isinstance(newproof, Proof)
        assert newproof.proven_truth.expr == self._expr
        self._proofs.add(newproof)

    def discard(self, oldproof):
        from .proof import Proof
        assert isinstance(oldproof, Proof)
        assert oldproof.proven_truth.expr == self._expr
        assert not oldproof.is_possibly_usable(), (
                "Should only remove unusable proofs")
        self._proofs.discard(oldproof)

    def best_proof(self, judgment):
        '''
        Return the best proof applicable to the judgment that is usable
        (or None if there aren't any that are usable).
        '''
        assert isinstance(judgment, Judgment)
        best_unusable_proof = None
        goodness = None
        for proof in self._proofs:
            if proof.proven_truth.assumptions.issubset(
                    judgment.assumptions):
                if proof.is_possibly_usable():
                    cur_goodness = proof._goodness()
                    if goodness is None or cur_goodness > goodness:
                        goodness = cur_goodness
                        best_unusable_proof = proof
        # the proof with the fewest steps that is applicable
        return best_unusable_proof  


class Judgment:
    # expr_to_judgments maps each Expression to a set of Judgments for
    # proving the Expression under various assumptions.
    expr_to_judgments = dict()

    # Map canonical form Expressions to sets of proven Expressions
    # with that canonical form.
    canonical_form_to_proven_exprs = dict()

    # Call the begin_proof method to begin a proof of a Theorem.
    theorem_being_proven = None  # Theorem being proven.
    theorem_being_proven_str = None # in string form.
    stored_theorem_being_proven = None # as a 'stored' theorem.
    # Have we already reported that the theorem is readily provable?
    theorem_readily_provable = None  
    # Goes from None to False (after beginning a proof and disabling 
    # Theorems that cannot be used) to True (when there is a legitimate
    # proof).

    # Set of theorems/theories that may (allowed) or may not
    # (disallowed) by presumed while proving the 'theorem_being_proven'.
    allowed_theorems_and_theories = None
    disallowed_theorems_and_theories = None
    presumed_theorems_and_dependencies = None
    
    qed_in_progress = False  # set to true when "%qed" is in progress

    # Judgments for which derive_side_effects is in progress, tracked to 
    # prevent infinite recursion when deducing side effects after 
    # something is proven.
    in_progress_to_derive_sideeffects = set()

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information in
        the Judgment jurisdiction.
        '''
        Judgment.expr_to_judgments.clear()
        Judgment.canonical_form_to_proven_exprs.clear()
        Judgment.theorem_being_proven = None
        Judgment.theorem_being_proven_str = None
        Judgment.stored_theorem_being_proven = None
        Judgment.theorem_readily_provable = None
        Judgment.allowed_theorems_and_theories = None
        Judgment.disallowed_theorems_and_theories = None
        Judgment.presumed_theorems_and_dependencies = None
        Judgment.qed_in_progress = False
        _ExprProofs.all_expr_proofs.clear()
        assert len(Judgment.in_progress_to_derive_sideeffects) == 0, (
                "Unexpected remnant 'in_progress_to_derive_sideeffects' "
                "items (should have been temporary)")

    def __init__(self, expression, assumptions, *, num_lit_gen=0):
        '''
        Create a Judgment with the given Expression, set of assumptions,
        and number of literal generalizations involved in the proof.

        These should NOT be created manually but rather through the 
        creation of Proofs which should be done indirectly via 
        Expression/Judgment derivation-step methods.
        '''
        # do some type checking
        if not isinstance(expression, Expression):
            raise ValueError(
                'The expression (expr) of a Judgment should be an Expression')
        for assumption in assumptions:
            if not isinstance(assumption, Expression):
                raise ValueError('Each assumption should be an Expression')
        if not isinstance(num_lit_gen, int):
            raise TypeError("'num_lit_gen' should be an Integer")

        # Note: these contained expressions are subject to style changes
        # on a Judgment instance basis.
        self.expr = expression
        # Store the assumptions as an ordered set (with the desired 
        # order for display).
        self.assumptions = OrderedSet(assumptions, mutable=False)
        
        # Associate the canonical form of the expression
        # with this Judgment.
        if defaults.sideeffect_automation:
            Judgment.canonical_form_to_proven_exprs.setdefault(
                    expression.canonical_form(), set()).add(expression)

        # We use the number of literal generalizations to distinguish
        # truths with different axiom/theorem eliminations; we assume
        # we won't have distinct literal generalization trees in the
        # same proof such that this is a distinguishing feature.
        self.num_lit_gen = num_lit_gen

        # The meaning data is shared among Judgments with the same
        # structure disregarding style
        def meaning_id_fn(expr): return hex(
            expr._establish_and_get_meaning_id())
        self._meaning_data = meaning_data(
            self._generate_unique_rep(meaning_id_fn))
        if not hasattr(self._meaning_data, '_expr_proofs'):
            # create or assign the _ExprProofs object for storing all 
            # proofs for this Judgment's expr (under any set of 
            # assumptions).
            if (self.expr, num_lit_gen) in _ExprProofs.all_expr_proofs:
                expr_proofs = _ExprProofs.all_expr_proofs[(self.expr, 
                                                           num_lit_gen)]
            else:
                expr_proofs = _ExprProofs(self.expr, num_lit_gen)
            self._meaning_data._expr_proofs = expr_proofs
            # Initially, _proof is None but will be assigned and updated
            # via _add_proof()
            self._meaning_data._proof = None

        # The style data is shared among Judgments with the same 
        # structure and style.
        self._style_data = style_data(
            self._generate_unique_rep(
                lambda expr: hex(
                    expr._style_id)))

        # reference this unchanging data of the unique 'meaning' data
        self._meaning_id = self._meaning_data._unique_id
        self._expr_proofs = self._meaning_data._expr_proofs

        self._style_id = self._style_data._unique_id

        # The _proof can change so it must be accessed via indirection 
        # into self._meaning_data (see proof() method).

    def _generate_unique_rep(self, object_rep_fn):
        '''
        Generate a unique representation string using the given function
        to obtain representations of other referenced Prove-It objects.
        '''
        # Note, the number of literal generalizations is a unique
        # aspect we include; more literal generalization typically means
        # fewere axiom/theorem requirements.
        rep = (
            object_rep_fn(self.expr) + ';[' + ','.join(
                object_rep_fn(assumption) for assumption in self.assumptions)
            + ']')
        if self.num_lit_gen > 0:
            rep += str(self.num_lit_gen)
        return rep

    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of 
        representations of Prove-It objects that are referenced.
        '''
        # Everything between the punctuation, ';', '[', ']', ',', is a
        # represented object.
        # Skip the 'num_lit_gen' part.
        last_rbracket_pos = unique_rep.rfind(']')
        obj_ids = re.split(r";|\[|,|\]", unique_rep[:last_rbracket_pos])
        return [obj_id for obj_id in obj_ids if len(obj_id) > 0]

    def derive_side_effects(self):
        '''
        Derive any side-effects that are obvious consequences arising 
        from this truth.  Called after the corresponding Proof is 
        complete.
        '''
        from .proof import ProofFailure, UnsatisfiedPrerequisites
        if not defaults.sideeffect_automation:
            return  # automation disabled
        if Judgment.theorem_being_proven == self:
            return # No need to derive side-effects now.
        if self not in Judgment.in_progress_to_derive_sideeffects:
            # avoid infinite recursion by using
            # in_progress_to_deduce_sideeffects
            Judgment.in_progress_to_derive_sideeffects.add(self)
            try:
                for side_effect in self.expr.side_effects(self):
                    # Attempt each side-effect derivation, specific to 
                    # thetype of Expression.
                    try:
                        # use the default assumptions which are 
                        # temporarily set to the assumptions utilized
                        # in the last derivation step.
                        side_effect()
                    except (ProofFailure, UnsatisfiedPrerequisites):
                        pass
                    except Exception as e:
                        raise Exception(
                            "Side effect failure for %s, while running %s: " %
                            (str(
                                self.expr),
                                str(side_effect)) +
                            str(e))
            finally:
                Judgment.in_progress_to_derive_sideeffects.remove(self)

    def order_of_appearance(self, sub_expressions):
        '''
        Yields the given sub-Expressions in the order in which they
        appear in this Judgment.  There may be repeats.
        '''
        for assumption in self.assumptions:
            for expr in assumption.order_of_appearance(sub_expressions):
                yield expr
        for expr in self.expr.order_of_appearance(sub_expressions):
            yield expr

    def __eq__(self, other):
        if isinstance(other, Judgment):
            return self._meaning_id == other._meaning_id
        else:
            # other must be an Expression to be equal to self
            return False  

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._meaning_id

    def begin_proof(self, theorem):
        '''
        Begin a proof for a theorem.  Only use other theorems that
        are explicitly allowed as presumptions for this theorem.
        Query the user when attempting to use a theorem that is neither
        allowed or disallowed.  If there exists any allowed presumed 
        theorem that has a direct or indirect dependence upon this 
        theorem then a CircularLogic exception is raised.
        '''
        from .proof import Theorem
        if Judgment.theorem_being_proven is not None:
            raise ProofInitiationFailure(
                "May only begin_proof once per Python/IPython session. "
                "Restart the notebook to restart the proof.")
        if not isinstance(theorem, Theorem):
            raise TypeError('Only begin a proof for a Theorem')
        if theorem.proven_truth != self:
            raise ValueError(
                'Inconsistent theorem for the Judgment in begin_proof call')

        # The lists of theorems/theories that are allowed/disallowed
        # to be presumed while proving this theorem.
        allowed, disallowed = theorem.get_allowed_and_disallowed_presumptions()

        self_str = str(self)
        if self_str in allowed:
            # A theorem may not presume itself!
            from .proof import CircularLogic
            raise CircularLogic(theorem, theorem)
        if self_str not in disallowed:
            # It goes without saying that we cannot presume the
            # theorem we are trying to prove.
            disallowed.add(self_str)

        Judgment.theorem_being_proven = theorem
        Judgment.theorem_being_proven_str = str(theorem)
        Judgment.stored_theorem_being_proven = theorem._stored_theorem()
        Judgment.allowed_theorems_and_theories = allowed
        Judgment.disallowed_theorems_and_theories = disallowed
        Judgment.presumed_theorems_and_dependencies = set()
        Theorem.update_usability()

        # change Judgment.has_been_proven
        # from None to False -- we can now test to see if
        # we have a proof for Judgment.theorem_being_proven
        Judgment.theorem_readily_provable = False

        # can't use itself to prove itself
        theorem._meaning_data._unusable_proof = theorem
        return self.expr

    def _qed(self):
        '''
        Complete a proof that began via `begin_proof`, entering it into
        the certification database.
        '''
        if Judgment.theorem_being_proven is None:
            raise Exception('No theorem being proven; cannot call qed method')
        if self.expr != Judgment.theorem_being_proven.proven_truth.expr:
            raise Exception('qed does not match the theorem being proven')
        if len(self.assumptions) > 0:
            raise Exception(
                'qed proof should not have any remaining assumptions')
        Judgment.qed_in_progress = True
        try:
            proven_truth = self.expr.prove(assumptions=[])
            if not proven_truth.is_usable():
                defaults._proven_truth = proven_truth
                proven_truth.raise_unusable_proof()
            print("{} has been proven.".format(Judgment.theorem_being_proven))
            Judgment.stored_theorem_being_proven._recordProof(proven_truth.proof())
        finally:
            Judgment.qed_in_progress = False
        return proven_truth.proof()

    def proof(self):
        '''
        Returns the most up-to-date proof of this Judgment.
        '''
        return self._meaning_data._proof
    
    def reprove(self, *, assumptions, new_style_expr=None):
        '''
        Reprove under new assumptions.  The original assumptions should be
        provable by these assumptions.  If provided, the new_style_expr
        should have the same meaning as the original proven expression
        but with a new style to be used.
        '''
        if new_style_expr is None or (
                new_style_expr._style_id == self._style_id):
            if len(assumptions) == len(self.assumptions) and all(
                    _orig_assump._style_id==_new_assump._style_id
                    for _orig_assump, _new_assump in
                    zip(self.assumptions, assumptions)):
                # No change.  No need to reprove.
                return self
        proof = self.proof().regenerate_proof_under_new_assumptions(
            assumptions=assumptions, new_style_expr=new_style_expr)
        return proof.proven_truth

    def is_possibly_usable(self):
        '''
        Returns True iff this Judgment has a proof that is "possibly
        usable" (not explicitly disallowed as a means to avoid circular
        dependencies).
        '''
        proof = self.proof()
        return proof is not None and proof.is_possibly_usable()
    
    def is_usable(self):
        '''
        Returns True iff this Judgment has a proof that is allowable
        as a presumption (there is either no "theorem being proven"
        or the theorem being proven explicitly allows all theorems
        used in the proof).  If the proof is neither explicitly allowed
        nor disallowed, the user will be queried to make the choice.
        '''
        proof = self.proof()
        if proof is None or not proof.is_possibly_usable(): 
            return False
        if proof.explicitly_allowed():
            return True
        # Neither explicitly allowed nor disallowed.  Query the
        # user to make a choice.
        while not proof._query_allowance():
            if self.proof() == proof:
                return False
            proof = self.proof() # proof was updated, so try again.
        return True

    def is_applicable(self, assumptions=USE_DEFAULTS):
        '''
        Return True iff this Judgment is usable and applicable under 
        the default assumptions.  Also, if it is applicable, make sure
        the side-effects are derived if sideeffect_automation is on
        in case it was off when the Judgment was proven.
        '''
        if assumptions is USE_DEFAULTS:
            assumptions = defaults.assumptions
        applicable = (self.is_possibly_usable() and 
                self.assumptions.issubset(assumptions))
        if applicable:
            # Make sure the side-effects are derived if sideeffect
            # automation is on in case it was off before.  This is
            # a good place to do it since we should check applicability
            # before using a Judgment.
            self.proof()._derive_side_effects()
        return applicable

    def as_theorem_or_axiom(self):
        '''
        Assuming this Judgment represents a Theorem or Axiom, return
        the Theorem or Axiom object.
        '''
        from .proof import Theorem, Axiom
        # Get the theorem associated with the Judgment (or raise an exception
        # if there is none)
        if Judgment.theorem_being_proven is not None:
            if self.expr == Judgment.theorem_being_proven.proven_truth.expr:
                return Judgment.theorem_being_proven
        proof = self.proof()
        if isinstance(proof, Theorem) or isinstance(proof, Axiom):
            return proof
        else:
            raise ValueError("Judgment does not represent a theorem or axiom.")

    def print_requirements(self):
        '''
        Provided that this Judgment is known to represent a proven
        theorem, print the set of axioms that are required directly or 
        indirectly inits proof as well as any required theorems that are
        unproven (if it has not yet been proven completely).
        '''
        from proveit.certify import is_fully_proven, all_requirements
        # print the required axioms and unproven theorems
        required_axioms, required_theorems = all_requirements(self)
        for axiom in sorted(required_axioms):
            print(axiom)
        if len(required_theorems) == 0:
            assert is_fully_proven(self), "certification database is corrupt"
            print("Theorem is fully proven!")
        if len(required_theorems) > 0:
            assert not is_fully_proven(
                self), "certification database is corrupt"
            print("\n_unproven theorems:")
            for theorem in sorted(required_theorems):
                print(theorem)

    def print_dependents(self):
        '''
        Provided that this Judgment is known to represent a theorem or 
        axiom, print all theorems that are known to depend on it 
        directly or indirectly.
        '''
        from proveit.certify import all_dependents
        dependents = all_dependents(self)
        for theorem in sorted(dependents):
            print(theorem)

    def _discard_proof(self, proof):
        '''
        Discard a disabled proof as an option in the _ExprProofs object.
        Don't change self._meaning_data._proof, now, however.  It will 
        be updated in due time and may be replaced with a proof that 
        hasn't been disabled.
        '''
        self._expr_proofs.discard(proof)

    def _add_proof(self, newproof=None):
        '''
        After a Proof is finished being constructed, record the best
        proof for the Judgment which may be the new proof, 'newproof',
        or a pre-existing one.  Update other Judgments that use the
        same 'truth' expression as needed.
        '''
        from .proof import _ShowProof
        # Update Judgment.expr_to_judgments; find all of the Judgments
        # with this expr to see if the proof should be updated with the
        # new proof.

        if self._meaning_data._proof == newproof:
            return # Not a new proof.

        if not newproof.is_possibly_usable():
            # Don't bother with a disabled proof unless it is the only
            # proof.  in that case, we record it so we can generate a 
            # useful error message via raise_unusable_proof(..).
            if self._meaning_data._proof is None:
                self._meaning_data._proof = newproof
            return
        self._expr_proofs.insert(newproof)

        # Check to see if the new proof is applicable to any other 
        # Judgment.  It can replace an old proof if it became unusable 
        # or if the newer one uses fewer steps.
        #newproof_numsteps = newproof.num_steps()
        expr_judgments = Judgment.expr_to_judgments.setdefault(self.expr, 
                                                               set())
        expr_judgments.add(self)
        for expr_judgment in expr_judgments:
            if expr_judgment.num_lit_gen != self.num_lit_gen:
                # Must match the number of literal generalization steps.
                continue
            # Is 'newproof' applicable to 'expr_judgment'?
            if newproof.proven_truth.assumptions.issubset(
                    expr_judgment.assumptions):
                # replace if there was no pre-existing usable proof or 
                # the new proof has more literal generalization steps
                # (which can lead to fewer axiom/theorem requirements)
                # or the new proof is "better".
                preexisting_proof = expr_judgment.proof()
                if isinstance(preexisting_proof, _ShowProof):
                    continue
                if (preexisting_proof is None or
                        not preexisting_proof.is_possibly_usable() or
                        (newproof._goodness() > 
                         preexisting_proof._goodness())):
                    # replace an old proof
                    expr_judgment._update_proof(newproof)

    def _revise_proof(self):
        '''
        After a proof and its dependents have been disabled, we will see
        if there is another proof that is usable (see Proof.disable()).
        Return True iff the proof actually changed to something usable.
        '''
        return self._update_proof(self._expr_proofs.best_proof(self))

    def _update_proof(self, new_proof):
        '''
        Update the proof of this Judgment.  Return True iff the proof 
        actually changed to something usable.
        '''
        meaning_data = self._meaning_data

        if new_proof is None:
            # no usable proof.
            # no need to update dependencies because that would have 
            # already been done when the proof was disabled.
            if meaning_data._proof is not None:
                assert not meaning_data._proof.is_possibly_usable(), (
                        "should not update to an unusable new proof "
                        "if the old one was usable")
            return False  # did not change to something usable
        assert new_proof.is_possibly_usable(), (
                "Should not update with an unusable proof")

        if meaning_data._proof is None:
            # no previous dependents to update
            meaning_data._proof = new_proof
            return True  # new usable proof
        elif meaning_data._proof == new_proof:
            return False  # no change

        # swap out the old proof for the new proof in all dependencies
        meaning_data._proof._update_dependencies(new_proof)
        meaning_data._proof = new_proof  # set to the new proof

        return True

    @staticmethod
    def _check_if_ready_for_qed():
        if Judgment.theorem_readily_provable is None:
            return # A theorem proof hasn't been started.
        theorem_being_proven = Judgment.theorem_being_proven
        theorem_expr = Judgment.theorem_being_proven.proven_truth.expr
        if theorem_expr.readily_provable():
            if not Judgment.theorem_readily_provable:
                Judgment.theorem_readily_provable = True
                if theorem_expr.proven():
                    proven_truth = theorem_expr.prove(automation=False)
                    if proven_truth.is_usable():
                        print(
                            '%s has been proven. ' %
                            theorem_being_proven.name,
                            r'Now simply execute "%qed".')
                else:
                    print(
                        '%s may now be readily provable (assuming required '
                        'theorems are usable). '%theorem_being_proven.name,
                        r'Simply execute "%qed".')

    def __setattr__(self, attr, value):
        '''
        Judgments should be read-only objects.  Attributes may be added, 
        however; for example, the 'png' attribute which will be added
        whenever it is generated).   Also, _proof is an exception which 
        can be updated internally.
        '''
        if attr != '_proof' and attr in self.__dict__:
            raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value

    def __getattr__(self, name):
        '''
        The Judgment aquires the attributes of its Expression, so it 
        will act like the Expression except it has additional (or 
        possibly overridden) attributes.  When accessing functions of 
        the Expression, if that function has 'assumptions' as a keyword
        argument, the assumptions of the Judgment are automatically
        included.
        '''
        from proveit import defaults, USE_DEFAULTS

        # called only if the attribute does not exist in Judgment 
        # directly
        if name == 'png':
            raise AttributeError(
                "Do not use the Expression version of the 'png' "
                "attribute.")
        attr = getattr(self.expr, name)

        if hasattr(attr, '__call__'):
            if name[:4] == 'with':
                # 'with...' methods change the style.  We want to
                # change the style and the return the judgment.
                def call_method_for_new_style(*args, **kwargs):
                    new_style_expr = attr.__call__(*args, **kwargs)
                    return self.with_matching_styles(
                        new_style_expr, self.assumptions)
                return call_method_for_new_style
            sig = signature(attr)
            if ('defaults_config' in sig.parameters and
                    (sig.parameters['defaults_config'].kind 
                     == Parameter.VAR_KEYWORD)):
                # The attribute is a callable function with
                # 'defaults_config' as an argument (e.g., a prover).
                # Automatically include the Judgment assumptions.
                @wraps(attr)
                def call_method_with_judgment_assumptions(
                        *args, **defaults_config):
                    if len(self.assumptions) > 0:
                        # Include assumptions of the Judgment.
                        assumptions = defaults_config.get(
                                'assumptions', None)
                        if assumptions is None: 
                            assumptions=defaults.assumptions
                        if not self.assumptions.issubset(assumptions):
                            defaults_config['assumptions'] = \
                                OrderedSet(assumptions) + self.assumptions
                    return attr.__call__(*args, **defaults_config)
                return call_method_with_judgment_assumptions

        return attr

    def __dir__(self):
        '''
        The Judgment aquires the attributes of its Expression as well as 
        its own attributes.
        '''
        return sorted(set(dir(self.__class__) +
                          list(self.__dict__.keys()) + dir(self.expr)))

    def with_matching_style(self, expr):
        '''
        Return the Judgement with the style for the right of the
        turnstile matching the given expression.
        '''
        if expr != self.expr:
            raise ValueError(
                "Cannot match styles when expressions do "
                "not have the same meaning: %s ≠ %s."%(self.expr, expr))
        if expr._style_id == self.expr._style_id:
            return self # Nothing has changed
        return Judgment(expr, self.assumptions, 
                        num_lit_gen=self.num_lit_gen)

    def with_matching_styles(self, expr, assumptions):
        '''
        Return the Judgment with the styles matching
        those of the given expression and assumptions.
        '''
        if expr != self.expr:
            raise ValueError(
                "Cannot match styles when expressions are do "
                "not have the same meaning: %s ≠ %s."%(self.expr, expr))
        
        new_style_expr = expr
        new_style_assumptions = []
        for assumption in assumptions:
            if assumption in self.assumptions:
                new_style_assumptions.append(assumption)
        if ((new_style_expr._style_id == self.expr._style_id) and
                tuple(self.assumptions) == tuple(new_style_assumptions) and
                all(new_style_assumption._style_id == old_assumption._style_id
                    for new_style_assumption, old_assumption in zip(
                            new_style_assumptions, self.assumptions))):
            # Nothing has changed.
            return self
        
        if self.proof() is not None:
            return self.reprove(assumptions=assumptions, new_style_expr=expr)
        
        return Judgment(new_style_expr, new_style_assumptions,
                        num_lit_gen=self.num_lit_gen)

    @staticmethod
    def find_judgment(expression, assumptions, *,
                      allow_indirect_proven_assumptions=False,
                      allow_indirect_provable_assumptions=False):
        '''
        Try to find a Judgment for this expression that applies to
        the given set of assumptions.  The Judgment applies to the given
        assumptions if its assumptions are a subset of the given assumptions
        or, if allow_indirect_proven_assumptions=True, it's assumptions are 
        proven under the given assumptions or, if
        allow_indirect_provable_assumptions is True, it's assumptions are 
        provable under the given assumptions.
        Return None if there is no match.
        '''
        if expression not in Judgment.expr_to_judgments:
            return None
        truths = Judgment.expr_to_judgments[expression]
        suitable_truths = []
        
        for truth in truths:
            if len(truth.assumptions)==1 and  (
                    next(iter(truth.assumptions)) == truth.expr):
                # Must be a simple Assumption proof.
                continue # Avoids infinite recursion.
            proof = truth.proof()
            if proof is not None and proof.is_possibly_usable():
                if truth.assumptions.issubset(assumptions):
                    suitable_truths.append(truth)
                elif allow_indirect_proven_assumptions and all(
                        _assumption.proven(assumptions=assumptions) for
                        _assumption in truth.assumptions):
                    suitable_truths.append(truth)
                elif allow_indirect_provable_assumptions and all(
                        _assumption.readily_provable(assumptions=assumptions)
                        for _assumption in truth.assumptions):
                    suitable_truths.append(truth)                    
        if len(suitable_truths) == 0:
            return None  # no suitable truth
        # return one with the shortest proof, and among those the fewest
        # assumptions
        best_judgment = max(suitable_truths,
                            key=lambda truth: truth.proof()._goodness())
        '''
        Is this necessary?  with_matching_styles is used in
        Expression.prove and seems like it's handling this job in any case.
        
        # Make sure we get the desired style (and labels) for the
        # assumptions and 'truth'.
        # Although this looks vacuous, it will map an assumption of
        # any style to the assumption of the desired style.
        assumptions_with_style = {assumption: assumption for
                                  assumption in assumptions}
        if (best_judgment.expr._style_id != expression._style_id or
                any(assumption._style_id != assumptions_with_style[assumption]
                    for assumption in best_judgment.assumptions)):
            assumptions = [assumptions_with_style[assumption] for assumption in
                           best_judgment.assumptions]
            return best_judgment.with_matching_styles(expression,
                                                      assumptions)
        '''
        return best_judgment

    @staticmethod
    def forget_judgments():
        '''
        Forget all Judgment's and all Assumption proof objects.  This is
        used for demonstration purposes in the tutorial, but should not 
        generally be needed.
        '''
        from proof import Assumption
        Judgment.expr_to_judgments.clear()
        Assumption.all_assumptions.clear()

    def _checkedTruth(self, proof):
        proven_truth = proof.proven_truth
        if not proven_truth.is_possibly_usable():
            proven_truth.raise_unusable_proof()
        return proven_truth

    """
    def relabel(self, relabel_map):
        '''
        Performs a relabeling derivation step, deriving another Judgment
        from this Judgment, under the same assumptions, with relabeled
        Variables.  A Variable may only be relabeled to a Variable.
        Returns the proven relabeled Judgment, or throws an exception if the proof fails.
        '''
        from proveit._core_.proof import Specialization
        return self._checkedTruth(Specialization(self, num_forall_eliminations=0, relabel_map=relabel_map, assumptions=self.assumptions))
    """

    @prover
    def instantiate(self, repl_map=None, *, num_forall_eliminations=None,
                    simplify_only_where_marked=False,
                    markers_and_marked_expr=None,
                    **defaults_config):
        '''
        Performs an instantiation derivation step to be proven under the 
        given assumptions, in addition to the assumptions of the 
        Judgment.  This may instantiate Variables that are universally 
        quantified immediately to the right of the Judgment turnstile
        according to the "replacement" map (repl_map), eliminating the 
        quantifier as the corresponding variables are instantiated.
        It may eliminate any number of nested Forall operations, 
        instantiating the instance Variables according to repl_map, 
        going to the depth for which the instance variables occur as 
        keys in repl_map or according to num_forall_eliminations if it
        is specified.
        
        For Variables that map to Variables in the replacement map,
        this is handled as a relabeling across both sides of the
        turnstile as well as "internal" Lambda map parameters.
        For Variables that map to non-Variables, the replacement only
        occurs within an eliminated quantifier and will not penetrate 
        into internal Lambda maps that use that Variable as a parameter. 
        
        Replacements are made simultaneously.  For example, the 
        {x:y, y:x} mapping will swap x and y variables.
        
        If equality 'replacements' are specified or 'auto_simplify'
        is True (in proveit.defaults which may be temporarily set
        via keyword arguments), equality replacements may be made
        in the process via equality judgements where the left-hand-side
        is the expression being replaced and the right-hand-side is the
        replacement.

        If simplify_only_where_marked= is True, Prove-It will only 
        simplify "marked" parts of an expression.  
        'markers_and_marked_expr' must then be a tuple: Variable 
        markers, and an expression that matches pre-simplified 
        instantiated expression except where marked with the markers.
        Only sub-expressions containing a marker may be simplified
        (if auto_simplify=True).
        
        Returns the proven instantiated Judgment, or throws an exception
        if the proof fails.  For the proof to succeed, all conditions of
        eliminated Forall operations, after replacements are made, must
        be proven.  Furthermore, there may be additional requirements 
        when iterated parameters are instantiated (see Lambda.apply for
        details).  Automation may be used in attempting to prove these 
        requirements provided proveit.defaults.conclude_automation=True.
        '''
        from proveit import (Variable, Operation, Conditional, Lambda,
                             single_or_composite_expression,
                             ExprTuple, ExprRange, IndexedVar)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            get_param_var
        from proveit.logic import Forall
        from .proof import Theorem, Instantiation, ProofFailure
        
        if not self.is_possibly_usable():
            # If this Judgment is not usable, see if there is an alternate
            # under the set of assumptions that is usable.
            try:
                alternate = self.expr.prove(automation=False)
            except ProofFailure:
                self.raise_unusable_proof()
            return alternate.instantiate(repl_map)
        _proof = self.proof()

        # If no repl_map is provided, instantiate the 
        # "explicit_instance_vars" of the Forall with default mappings
        # (mapping instance variables to themselves)
        if repl_map is None:
            repl_map = {ivar: ivar for ivar in self.explicit_instance_vars()}

        # For any entrys in repl_map with Operation keys, convert
        # them to corresponding operator keys with Lambda substitutions.
        # For example f(x,y):g(x,y) would become f:[(x,y) -> g(x,y)].
        # And any ExprTuple-wrapped ExprRange entries will be
        # Also, convert to composite expressions as needed
        # (via single_or_composite_expression).
        processed_repl_map = dict()
        equiv_alt_expansions = dict()
        for key, replacement in repl_map.items():
            replacement = single_or_composite_expression(replacement)
            '''
            if isinstance(replacement, ExprRange):
                raise TypeError("Not expecting an ExprRange for a replacement "
                                "when instantiating.  Got %s.  Perhaps it "
                                "should be wrapped in an ExprTuple."
                                %replacement)
            '''
            if isinstance(key, ExprTuple) and key.is_single():
                # The key is an ExprTuple but is single -- so
                # just take it, and its replacement, out of
                # ExprTuple wrappers.
                if not (isinstance(replacement, ExprTuple)
                        and replacement.is_single()):
                    raise TypeError(
                        "%s is not the expected kind of replacement "
                        "for an ExprTuple key, %s"%(replacement, key))
                key = key[0]
                replacement = replacement[0]
            if isinstance(key, Variable) or isinstance(key, IndexedVar):
                processed_repl_map[key] = replacement
            elif isinstance(key, ExprTuple) and key.num_entries() > 0:
                try:
                    for param_entry in key:
                        get_param_var(param_entry)
                except (ValueError, TypeError) as e:
                    raise TypeError(
                        "%s is not the expected kind of Expression "
                        "as a repl_map key:\n%s" %
                        (key, str(e)))
                if key.num_entries() == 1:
                    # Replacement key for replacing a range of indexed
                    # variables, or range of ranges of indexed variables
                    # , etc.
                    processed_repl_map[key] = replacement
                    # Although this is redundant (not really necessary
                    # as an entry in `equiv_alt_expansions` as far
                    # as Lambda.apply is concerned) it is useful for
                    # bookkeeping to extract all of the instantiation
                    # mappings:
                    equiv_alt_expansions[key] = replacement
                else:
                    assert key.num_entries() > 1
                    # An "alternative equivalent expansion" of
                    # some range of indexed variables (or range of 
                    # ranges, etc.).    For example,
                    # (x_i, x_{i+1}, ..., x_j).
                    equiv_alt_expansions[key] = replacement
            elif (isinstance(key, Operation) 
                    and isinstance(key.operator, Variable)):
                operation = key
                repl_var = operation.operator
                replacement = Lambda(operation.operands, replacement)
                processed_repl_map[repl_var] = replacement
            else:
                raise TypeError(
                    "%s is not the expected kind of Expression as "
                    "a repl_map key.  Expecting repl_map keys to be "
                    "Variables, Operations with Variable operators "
                    "(for operation substitution), or an ExprTuple "
                    "containing a single iterated IndexedVar "
                    "like (x_i, ..., x_j)." %
                    key)

        def get_repl_var(repl_key):
            if isinstance(repl_key, ExprTuple):
                return get_param_var(repl_key.entries[0])
            return get_param_var(repl_key)

        if num_forall_eliminations is None:
            # Determine the number of Forall eliminations.
            # The number is determined by the instance variables that
            # occur as keys in repl_map.
            expr = self.expr
            remaining_repl_vars = \
                {get_repl_var(repl_key) for repl_key
                 in processed_repl_map.keys()}
            forall_depth = 0
            num_forall_eliminations = 0
            while len(remaining_repl_vars) > 0:
                if not isinstance(expr, Forall):
                    # No more directly nested universal quantifiers
                    break  # to eliminate.
                lambda_expr = expr.operand
                assert isinstance(lambda_expr, Lambda), (
                    "Forall Operation operand must be a Lambda function")
                instance_param_vars = lambda_expr.parameter_vars
                expr = lambda_expr.body
                if isinstance(expr, Conditional):
                    # Skip over the "conditions" of the Forall expression.
                    expr = expr.value
                forall_depth += 1
                for iparam_var in instance_param_vars:
                    if iparam_var in remaining_repl_vars:
                        # Remove this instance parameter variable from
                        # the remaining variables to replace.
                        remaining_repl_vars.remove(iparam_var)
                        # Eliminate to this depth at least since there
                        # is a replacement map for the instance
                        # variable:
                        num_forall_eliminations = forall_depth
                    else:
                        # default is to map instance variables to
                        # themselves
                        processed_repl_map[iparam_var] = iparam_var
        temporarily_preserved_exprs = set()
        try:
            # Do not simplify any of the instantiation expressions since
            # there is a directive to specifically use them.  For
            # ExprTuple instantiations, do not simplify any of the
            # individual entries (this is important, for example, if
            # this is replacing just a portion of an ExprTuple).
            def gen_repl_vals_and_entries():
                for _repl_val in processed_repl_map.values():
                    yield _repl_val
                    if isinstance(_repl_val, ExprTuple):
                        for _entry in _repl_val:
                            yield _entry
            temporarily_preserved_exprs = (
                    set(gen_repl_vals_and_entries()) - 
                    defaults.preserved_exprs)
            # Explicit replacements, however, are allowed, unless there
            # is an explicit expression preservation to override it.
            for replacement in defaults.replacements:
                temporarily_preserved_exprs.discard(replacement.lhs)
            defaults.preserved_exprs.update(temporarily_preserved_exprs)

            return self._checkedTruth(
                Instantiation.get_instantiation(
                        self, num_forall_eliminations=num_forall_eliminations,
                        repl_map=processed_repl_map,
                        equiv_alt_expansions=equiv_alt_expansions,
                        simplify_only_where_marked=simplify_only_where_marked,
                        markers_and_marked_expr=markers_and_marked_expr))
        finally:
            # Revert the preserved_exprs set back to what it was.
            defaults.preserved_exprs.difference_update(
                    temporarily_preserved_exprs)

    def generalize(self, forall_var_or_vars_or_var_lists, *,
                   domain_lists=None, domain=None, conditions=tuple(),
                   antecedent=None):
        '''
        Performs a generalization derivation step.  Returns the
        proven generalized Judgment.  Can introduce any number of
        nested Forall operations to wrap the original statement,
        corresponding to the number of given forall_var_lists and 
        domains.  A single variable list or single variable and a single
        domain may be provided to introduce a single Forall wrapper.

        This will also handle "literal" generalization in which literals
        are converted to variables (with the same formatting), 
        corresponding axioms and/or theorems are converted to 
        assumptions, and these variables are then generalized in one 
        step.  To do this, simply supply Literal expressions in place of
        Variables in the forall_var_or_vars_or_var_lists.  There may
        even be a mixture of Literals and Variables.  There are 
        important limitations regarding literal generalization.  There 
        must not be any axiom or theorem requirement using that Literal
        that isn't masked by a condition, or a 
        LiteralGeneralizationFailure will be raised.  That is, *all* 
        needed axioms/theorems which use that Literal must be converted 
        to an assumption (with the Literal converted to a Variable) and 
        then included in the conditions (or antecedent).

        If an antecedent is provided, it plays the role of an extra
        condition but is placed in an implication instead of a
        Conditional.
        '''
        from proveit._core_.proof import Generalization
        from proveit._core_.expression.label import Literal
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            valid_params
        from proveit._core_.expression.composite.expr_tuple import \
            ExprTuple
        from proveit._core_.expression.composite.composite import \
            composite_expression
        from proveit.logic import InSet

        # Convert all forms of `forall_var_or_vars_or_var_lists` to
        # forall_var_lists, the most general form.  Start with the
        # default:
        forall_var_lists = forall_var_or_vars_or_var_lists
        try:
            forall_vars = composite_expression(forall_var_or_vars_or_var_lists)
            # Convert Literals to variables just to check to see
            # if this corresponds to a 1-level list of variable
            # parameters.
            _forall_vars = ExprTuple(
                *[_.as_variable() if isinstance(_, Literal)
                  else _ for _ in forall_vars.entries])
            if valid_params(_forall_vars):
                forall_var_lists = [forall_vars]
        except (ValueError, TypeError) as e:
            print(e)
            pass  # don't change the default

        if not hasattr(forall_var_lists, '__len__'):
            raise ValueError("Must supply 'generalize' with a "
                             "Variable/Literal, "
                             "list of Variables/Literals (or variable "
                             "ranges), or list of lists of Variables/"
                             "Literals (or variable ranges).")
        if len(forall_var_lists) == 0:
            raise ValueError(
                "Must provide at least one Variable to generalize over")

        for forall_var_list in forall_var_lists:
            if not hasattr(forall_var_lists, '__iter__'):
                raise ValueError(
                    "`forall_var_lists` must be a list of lists specifying "
                    "instance parameters of forall operations to "
                    "introduce (or, for convenience it may be a single "
                    "variable)")

        # Add domain conditions as appropriate
        if domain is not None and domain_lists is not None:
            raise ValueError("Either specify a `domain` or "
                             "'domain_lists' but not both")
        if domain is not None:
            domain_lists = [[domain] * len(forall_var_lists) for
                            forall_var_list in forall_var_lists]
        if domain_lists is not None:
            domain_conditions = []
            for domain_list, forall_var_list in zip(domain_lists,
                                                    forall_var_lists):
                domains = composite_expression(domain_list)
                forall_vars = composite_expression(forall_var_list)
                if domains.num_entries() == 1:
                    domains = [domain_list[0]] * forall_vars.num_entries()
                domain_conditions += [InSet(instance_var, domain) for
                                      instance_var, domain in
                                      zip(forall_vars, domains)]
            conditions = domain_conditions + list(conditions)

        return self._checkedTruth(Generalization(
            self, forall_var_lists, conditions, antecedent))

    def as_implication(self, hypothesis):
        '''
        Performs a "deduction" derivation step, forming an implication
        statement with the given hypothesis and self.expr
        as the conclusion.  The hypothesis is removed from the set of
        the conclusion statement's assumptions for the implication
        statement's assumptions.
        '''
        from proveit._core_.proof import Deduction
        if isinstance(hypothesis, Judgment):
            hypothesis = hypothesis.expr  # we want the expression for this purpose
        return self._checkedTruth(Deduction(self, hypothesis))

    def conservative_definition_lit(self):
        '''
        If this Judgment is in the form of a conservative definition
        for a Literal, then return that Literal; otherwise return None.
        To be of the propere form, it must not have any assumptions,
        and it must either be an equation with a Literal on the left
        side or a universally quantified equation with the left side
        being a function of a Literal applied to all of the quantified
        variables.
        '''
        from proveit import Literal, Operation
        from proveit.logic import Forall, Equals
        if len(self.assumptions) > 0: return None
        expr = self.expr
        if isinstance(expr, Equals):
            if isinstance(expr.lhs, Literal):
                # Simple equation with Literal on the left side.
                return expr.lhs
        # Otherwise, to have the form of a conservative definition,
        # it must be a universally quantified defining a function
        # of a Liiteral applied to all of the quantified variables.
        if not isinstance(expr, Forall):
            return None
        equality = expr.instance_expr
        if not isinstance(equality, Equals):
            return None # must universally quantify an equality
        if (not isinstance(equality.lhs, Operation) 
                or not isinstance(equality.lhs.operator, Literal)):
            # Must define an Operation with a Literal operator.
            return None
        if equality.lhs.operands != expr.instance_params:
            # The operands must match the instance parameters.
            return None
        return equality.lhs.operator

    """
    @prover
    def eliminate_definition(self, definition, *,
                             as_implication_internally=False, 
                             with_internal_wrapping=False,
                             **defaults_config):
        '''
        Using literal generalization and then instantiation, eliminate
        a required axiom or theorem that provides a conservative 
        (non-reflexive/recursive) definition of a literal in terms of 
        an equality or universal quantification over an equality (for 
        literals playing a function role) with the literal on the left
        of the equality.

        Setting as_implication to True will put the definition
        as the antecedant of an implication in the internal
        literal generalization step.  If the definition is quantified,
        an implication will always be used.

        Setting 'with_internal_wrapping' to True will wrap the
        the implication (if using an implication) or wrap the
        Forall for the internal literal generalization step.
        '''
        from proveit import Literal, Operation, Lambda, Conditional
        from proveit.logic import Equals, Forall

        def raise_type_error():
            raise TypeError("'definition' should be an equality or "
                            "universally quantified equality but got %s."
                            %definition)
        
        if isinstance(definition, Judgment):
            definition = definition.expr

        if isinstance(definition, Equals):
            if not isinstance(definition.lhs, Literal):
                raise TypeError("Expecting a Literal on the left side "
                                "of the 'definition' equality but got "
                                "%s."%definition.lhs)
            lit = definition.lhs
            var = lit.as_variable()
            condition = definition.literals_as_variables(lit)
            if as_implication_internally:
                gen = self.generalize(lit, antecedent=condition)
                if with_internal_wrapping:
                    gen = (gen.inner_expr().instance_expr
                           .with_wrap_before_operator())
                return (gen.instantiate({var:condition.rhs},
                                        preserve_all=True)
                        .derive_consequent())
            else:
                gen = self.generalize(lit, conditions=[condition])
                if with_internal_wrapping:
                    gen = gen.with_wrapping()
                return gen.instantiate({var:condition.rhs},
                                       preserve_all=True)

        if not isinstance(definition, Forall):
            raise_type_error()
        equality = definition.instance_expr
        if not isinstance(equality, Equals):
            raise_type_error()
        if (not isinstance(equality.lhs, Operation) 
                or not isinstance(equality.lhs.operator, Literal)):
            raise TypeError(
                "If universally quantified, the 'definition' "
                "should have an Operation with a Literal operator "
                "on the left side of the quantified equality.")
        if equality.lhs.operands != definition.instance_params:
            raise TypeError(
                "If universally quantified, the 'definition' "
                "should have an Operation on the left side of "
                "the quantified equality with operands matching "
                "the quantified parameters: %s ≠ %s"
                %(equality.lhs.operands, definition.instance_params))

        lit = equality.lhs.operator
        var = lit.as_variable()
        # Always use the antecedant form for a quantified
        # definition.
        antecedent = definition.literals_as_variables(lit)
        repl = Lambda(antecedent.instance_params,
                      antecedent.instance_expr.rhs)
        gen = self.generalize(lit, antecedent=antecedent)
        if with_internal_wrapping:
            gen = (gen.inner_expr().instance_expr
                   .with_wrap_before_operator())
        impl = gen.instantiate({var:repl}, auto_simplify=False)
        return impl.derive_consequent()
    """

    @prover
    def eliminate(self, *skolem_constants, **defaults_config):
        '''
        Performs a Skolem constant elimination derivation step on this
        Judgment (KT), where this KT has the form S |– alpha and the
        set S of assumptions includes one or more assumptions involving
        one or more Skolem constants sk1, …, skn specified by
        skolem_constants, where the Skolem constant-related assumptions
        were previously generated using the Exists.choose(sk1, …, skn)
        method.
        '''
        from proveit.logic import Exists
        return Exists.eliminate(skolem_constants, self)

    # Not a @prover since it just uses the assumptions of the Judgment. 
    def simplify(self):
        '''
        Prove a simplified form of this Judgment.
        '''
        with defaults.temporary() as temp_defaults:
            # Use the assumptions of the Judgment
            temp_defaults.assumptions = self.assumptions
            # Don't exploit the evaluation of the Judgment; it
            # must be TRUE (under its assumptions), but that's
            # trivial and useless.
            simplification = self.simplification(_no_eval_check=True)
            return simplification.derive_right_via_equality()
        
    # Not a @prover since it just uses the assumptions of the Judgment. 
    def evaluation(self):
        '''
        Prove that the Judgement expression equals TRUE
        under the assumptions of the Judgment.
        '''
        from proveit.logic import evaluate_truth
        return evaluate_truth(self.expr, assumptions=self.assumptions)

    def as_impl(self, hypothesis):
        '''
        Abbreviation for as_implication.
        '''
        return self.as_implication(hypothesis)

    def raise_unusable_proof(self):
        from .proof import UnusableProof
        proof = self.proof()
        unusuable_proof = proof._meaning_data._unusable_proof
        if proof == unusuable_proof:
            raise UnusableProof(Judgment.theorem_being_proven, unusuable_proof)
        else:
            raise UnusableProof(
                Judgment.theorem_being_proven, unusuable_proof,
                'required to prove' + self.string())

    def string(self):
        '''
        Display the turnstile notation to show that the judgment
        on the right derives from the set of assumptions on the left.
        '''
        from proveit import ExprTuple
        if len(self.assumptions) > 0:
            assumptions_str = ExprTuple(
                *
                self.assumptions).formatted(
                'string',
                fence=False)
            return r'{' + assumptions_str + r'} |- ' + self.expr.string()
        return r'|- ' + self.expr.string()

    def latex(self):
        '''
        Display the turnstile notation to show that the judgment
        on the right derives from the set of assumptions on the left.
        '''
        from proveit import ExprTuple
        if len(self.assumptions) > 0:
            assumptions_latex = ExprTuple(
                *
                self.assumptions).formatted(
                'latex',
                fence=False)
            return r'{' + assumptions_latex + r'} \vdash ' + self.expr.latex()
        return r'\vdash ' + self.expr.latex()

    def __str__(self):
        '''
        Return a string representation of the Judgment.
        '''
        return self.string()

    def __repr__(self):
        '''
        Return a string representation of the Judgment.
        '''
        if not self.is_possibly_usable():
            self.raise_unusable_proof()
        return self.string()

    def _repr_html_(self):
        '''
        Generate html to show the Judgment as a set of assumptions,
        turnstile, then the statement expression.  Expressions are png's
        compiled from the latex (that may be recalled from memory or
        storage if previously generated) with a links to
        expr.ipynb notebooks for displaying the expression information.
        '''
        if not defaults.display_latex:
            return None  # No LaTeX display at this time.
        if not self.is_usable():
            self.raise_unusable_proof()
        html = ''
        proof = self.proof()
        html += '<span style="font-size:20px;">'
        html += ', '.join(assumption._repr_html_() for assumption
                          in self.assumptions)
        html += ' '
        if proof is not None:
            # link to the proof
            html += ('<a class="ProveItLink" '
                     'href="%s" style="text-decoration: none">' 
                     % proof.get_link())
        html += '&nbsp;&#x22A2;&nbsp;&nbsp;'  # turnstile symbol
        if proof is not None:
            html += '</a>'
        html += self.expr._repr_html_()
        html += '</span>'
        return html

    def inner_expr(self, assumptions=USE_DEFAULTS):
        '''
        Return an InnerExpr object to wrap the Judgment and
        access any inner sub-expression (including assumptions or
        inner expressions of assumptions) for the purpose of
        replacing the inner expression, changing its style,
        or relabeling variables.
        '''
        from .expression.inner_expr import InnerExpr
        if assumptions==USE_DEFAULTS:
            assumptions=defaults.assumptions
        assumptions = OrderedSet(assumptions) + self.assumptions
        return InnerExpr(self, assumptions=assumptions)
    
    def _used_vars(self):
        '''
        Return all of the used Variables of this Judgment,
        including those in assumptions.
        Call externally via the used_vars method in expr.py.
        '''
        return self.expr._used_vars().union(
                *[assumption._used_vars() for
                  assumption in self.assumptions])

    def _contained_parameter_vars(self):
        '''
        Return all of the used parameter variables contained in this
        Judgment, including those in assumptions.
        Call externally via the contained_parameter_vars method
        in expr.py.
        '''
        return self.expr._contained_parameter_vars().union(
                *[assumption._contained_parameter_vars() for
                  assumption in self.assumptions])


def as_expression(truth_or_expression):
    '''
    Return the argument as Expressions.  That is, if the argument is the
    Judgment, yield its associated Expression.  If it is an Expression,
    yield just that.  Otherwise, raise a TypeError.
    '''
    if isinstance(truth_or_expression, Judgment):
        return truth_or_expression.expr
    elif isinstance(truth_or_expression, Expression):
        return truth_or_expression
    else:
        raise TypeError('Expected to be a Judgment or an Expression')


def as_expressions(*truth_or_expressions):
    '''
    Return the arguments as a list of Expressions via as_expression.
    '''
    return [as_expression(truth_or_expression)
            for truth_or_expression in truth_or_expressions]


class ProofInitiationFailure(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message
