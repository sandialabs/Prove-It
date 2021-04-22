"""
A Judgment represents an expression that has been proven to be a true
statement.  A Judgment wraps an Expression (acting like the Expression
in many ways via overloading __getattr__) but also has a list of assumptions
and its proof (as a Proof object, which may be updated if a newer proof,
with possibly fewer assumptions, suffices).
"""

from proveit._core_.expression import Expression
from proveit._core_._unique_data import meaning_data, style_data
from proveit.decorators import prover
from .defaults import defaults, USE_DEFAULTS
import re
from copy import copy


class _ExprProofs:
    '''
    Stores a set of proofs for a particular expression under any set
    of assumptions.  We maintain such sets so that we can update
    Judgment proofs appropriately when a particular proof has been
    disabled.
    '''
    all_expr_proofs = dict()  # map expressions to expression proofs

    def __init__(self, expr):
        self._expr = expr
        self._proofs = set()
        _ExprProofs.all_expr_proofs[expr] = self

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
        assert not oldproof.is_usable(), (
                "Should only remove unusable proofs")
        self._proofs.discard(oldproof)

    def best_proof(self, judgment):
        '''
        Return the best proof applicable to the judgment that is usable
        (or None if there aren't any that are usable).
        '''
        assert isinstance(judgment, Judgment)
        best_unusable_proof = None
        fewest_steps = float('inf')
        for proof in self._proofs:
            if proof.proven_truth.assumptions_set.issubset(
                    judgment.assumptions_set):
                assert proof.is_usable(), (
                        'unusable proofs should have been removed')

                if proof.num_steps() < fewest_steps:
                    fewest_steps = proof.num_steps()
                    best_unusable_proof = proof
        # the proof with the fewest steps that is applicable
        return best_unusable_proof  


class Judgment:
    # lookup_dict maps each Expression to a set of Judgments for
    # proving the Expression under various assumptions.
    lookup_dict = dict()

    # (Judgment, default assumptions) pairs for which 
    # derive_side_effects has been called.  We track this to make sure 
    # we didn't miss anything while automation was disabled and then 
    # re-enabled.
    sideeffect_processed = set()

    # Call the begin_proof method to begin a proof of a Theorem.
    theorem_being_proven = None  # Theorem being proven.
    theorem_being_proven_str = None # in string form.
    # Has the theorem_being_proven been proven yet in this session?
    has_been_proven = None  
    # Goes from None to False (after beginning a proof and disabling 
    # Theorems that cannot be used) to True (when there is a legitimate
    # proof).

    # Set of theorems/packages that are presumed to be True for the
    # purposes of the proof being proven and exclusions thereof:
    presumed_theorems_and_theories = None
    presuming_theorem_and_theory_exclusions = None
    
    # Set of theorems that have been presumed or their dependencies
    # (direct or indirect).
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
        Judgment.lookup_dict.clear()
        Judgment.sideeffect_processed.clear()
        Judgment.theorem_being_proven = None
        Judgment.theorem_being_proven_str = None
        Judgment.has_been_proven = None
        Judgment.presumed_theorems_and_theories = None
        Judgment.presuming_theorem_and_theory_exclusions = None
        Judgment.presumed_theorems_and_dependencies = None
        Judgment.qed_in_progress = False
        _ExprProofs.all_expr_proofs.clear()
        assert len(Judgment.in_progress_to_derive_sideeffects) == 0, (
                "Unexpected remnant 'in_progress_to_derive_sideeffects' "
                "items (should have been temporary)")

    def __init__(self, expression, assumptions):
        '''
        Create a Judgment with the given Expression, set of assumptions.
        These should not be created manually but rather through the 
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

        # Note: these contained expressions are subject to style changes
        # on a Judgment instance basis.
        self.expr = expression
        # Store the assumptions as an ordered list (with the desired 
        # order for display) and an unordered set (for convenience when 
        # checking whether one set subsumes another).
        self.assumptions = tuple(assumptions)
        self.assumptions_set = frozenset(assumptions)

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
            if self.expr in _ExprProofs.all_expr_proofs:
                expr_proofs = _ExprProofs.all_expr_proofs[self.expr]
            else:
                expr_proofs = _ExprProofs(self.expr)
            self._meaning_data._expr_proofs = expr_proofs
            # Initially, _proof is None but will be assigned and updated
            # via _addProof()
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
        return object_rep_fn(self.expr) + ';[' + ','.join(
            object_rep_fn(assumption) for assumption in self.assumptions) + ']'

    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of 
        representations of Prove-It objects that are referenced.
        '''
        # Everything between the punctuation, ';', '[', ']', ',', is a
        # represented object.
        obj_ids = re.split(r";|\[|,|\]", unique_rep)
        return [obj_id for obj_id in obj_ids if len(obj_id) > 0]

    def derive_side_effects(self):
        '''
        Derive any side-effects that are obvious consequences arising 
        from this truth.  Called after the corresponding Proof is 
        complete.
        '''
        from .proof import ProofFailure
        if not defaults.automation:
            return  # automation disabled
        # Sort the assumptions according to hash key so that sets of
        # assumptions are unique for determining which side-effects have
        # been processed already.
        assumptions = defaults.assumptions
        sorted_assumptions = tuple(
            sorted(assumptions, key=lambda expr: hash(expr)))
        if (self.expr, sorted_assumptions) in Judgment.sideeffect_processed:
            return  # has already been processed
        if self not in Judgment.in_progress_to_derive_sideeffects:
            # avoid infinite recursion by using
            # in_progress_to_deduce_sideeffects
            Judgment.in_progress_to_derive_sideeffects.add(self)
            try:
                for side_effect in self.expr.side_effects(self):
                    #print(self, "side-effect", side_effect)
                    # Attempt each side-effect derivation, specific to 
                    # thetype of Expression.
                    try:
                        # use the default assumptions which are 
                        # temporarily set to the assumptions utilized
                        # in the last derivation step.
                        side_effect()
                    except ProofFailure:
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
            Judgment.sideeffect_processed.add((self.expr, sorted_assumptions))

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
        Begin a proof for a theorem.  Only use other theorems that are 
        in the presuming list of theorems/packages or theorems that are 
        required, directly or indirectly, in proofs of theorems that are
        explicitly listed (these are implicitly presumed).  If there 
        exists any presumed theorem that has a direct or indirect 
        dependence upon this theorem then a CircularLogic exception is
        raised.
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

        # The full list of presumed theorems includes all previous 
        # theoremsof the theory and all indirectly presumed theorems 
        # via transitivity (a presumption of a presumption is a
        # presumption).
        presumptions, exclusions = theorem.get_presumptions_and_exclusions()

        if str(self) in presumptions:
            # A theorem may not presume itself!
            from .proof import CircularLogic
            raise CircularLogic(theorem, theorem)

        Judgment.theorem_being_proven = theorem
        Judgment.theorem_being_proven_str = str(theorem)
        Judgment.presumed_theorems_and_theories = presumptions
        Judgment.presuming_theorem_and_theory_exclusions = exclusions
        Judgment.presumed_theorems_and_dependencies = set()
        Theorem.update_usability()

        # change Judgment.has_been_proven
        # from None to False -- we can now test to see if
        # we have a proof for Judgment.theorem_being_proven
        Judgment.has_been_proven = False

        if self._checkIfReadyForQED(self.proof()):
            return self.expr  # already proven
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
            proof = self.expr.prove(assumptions=[]).proof()
            if not proof.is_usable():
                proof.proven_truth.raise_unusable_proof()
            Judgment.theorem_being_proven._recordProof(proof)
        finally:
            Judgment.qed_in_progress = False
        return proof

    def proof(self):
        '''
        Returns the most up-to-date proof of this Judgment.
        '''
        return self._meaning_data._proof

    def is_usable(self):
        '''
        Returns True iff this Judgment has a "usable" proof.  Proofs
        may be unusable when proving a theorem that is restricted with
        respect to which theorems may be used (to avoid circular logic).
        '''
        proof = self.proof()
        return proof is not None and proof.is_usable()

    def is_sufficient(self, assumptions):
        '''
        Return True iff the given assumptions satisfy the Judgment;
        the Judgment is usable and requires a subset of the given 
        assumptions.
        '''
        return self.is_usable() and self.assumptions_set.issubset(assumptions)

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

    def _discardProof(self, proof):
        '''
        Discard a disabled proof as an option in the _ExprProofs object.
        Don't change self._meaning_data._proof, now, however.  It will 
        be updated in due time and may be replaced with a proof that 
        hasn't been disabled.
        '''
        self._expr_proofs.discard(proof)

    def _addProof(self, newproof=None):
        '''
        After a Proof is finished being constructed, record the best
        proof for the Judgment which may be the new proof, 'proof',
        or a pre-existing one.  Update all Judgments
        with the same 'truth' expression that should be updated.
        '''
        # print 'record best', self.expr, 'under', self.assumptions
        # update Judgment.lookup_dict and use find all of the Judgments
        # with this expr to see if the proof should be updated with the
        # new proof.

        if not newproof.is_usable():
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
        expr_judgments = Judgment.lookup_dict.setdefault(self.expr, set())
        expr_judgments.add(self)
        for expr_judgment in expr_judgments:
            # Is 'proof' applicable to 'expr_judgment'?
            if newproof.proven_truth.assumptions_set.issubset(
                    expr_judgment.assumptions_set):
                # replace if there was no pre-existing usable proof or 
                # the new proof has fewer steps
                preexisting_proof = expr_judgment.proof()
                if (preexisting_proof is None or
                        not preexisting_proof.is_usable() or
                        newproof.num_steps() < preexisting_proof.num_steps()):
                    expr_judgment._updateProof(
                        newproof)  # replace an old proof

    def _reviseProof(self):
        '''
        After a proof and its dependents have been disabled, we will see
        if there is another proof that is usable (see Proof.disable()).
        Return True iff the proof actually changed to something usable.
        '''
        return self._updateProof(self._expr_proofs.best_proof(self))

    """
    def _recordBestProof(self, new_proof):
        '''
        After a Proof is finished being constructed, check to see if
        any proofs for this Judgment are obsolete; the new proof
        might make a previous one obsolete, or it may be born
        obsolete itself.  A proof is obsolete if there exists a Judgment
        with a subset of the assumptions required for that proof, or with
        the same set of assumptions but fewer steps.  A tie goes to the
        new proof, but note that the step number comparison will prevent
        anything cyclic (since a proof for a Judgment that requires that
        same Judgment as a dependent will necessarily include the
        number of steps of the original proof plus more).
        '''
        self._updateProof(self._expr_proofs.best_proof(self))


        from proof import Theorem
        if not self.expr in Judgment.lookup_dict:
            # the first Judgment for this Expression
            self._proof = new_proof
            Judgment.lookup_dict[self.expr] = [self]
            return
        if not new_proof.is_usable():
            # if it is not usable, we're done.
            if self._proof is None:
                # but first set _proof to the new_proof if there
                # is not another one.
                self._proof = new_proof
            return
        kept_truths = []
        born_obsolete = False
        for other in Judgment.lookup_dict[self.expr]:
            if self.assumptions_set == other.assumptions_set:
                if not other._proof.is_usable():
                    # use the new proof since the old one is unusable.
                    other._updateProof(new_proof)
                elif new_proof.num_steps <= other._proof.num_steps:
                    if new_proof.required_proofs != other._proof.required_proofs:
                        # use the new (different) proof that does the job as well or better
                        if isinstance(new_proof, Theorem):
                            # newer proof is a theorem; record the existing proof as a possible proof for that theorem
                            new_proof._possibleProofs.append(other._proof)
                        other._updateProof(new_proof)
                else:
                    # the new proof was born obsolete, taking more steps than an existing one
                    if isinstance(other._proof, Theorem):
                        # the older proof is a theorem, record the new proof as a possible proof for that theorem
                        other._proof._possibleProofs.append(new_proof)
                    self._proof = other._proof # use an old proof that does the job better
                    kept_truths.append(other)
                    born_obsolete = True
            elif self.assumptions_set.issubset(other.assumptions_set):
                # use the new proof that does the job better
                other._updateProof(new_proof)
            elif self.assumptions_set.issuperset(other.assumptions_set) and other._proof.is_usable():
                # the new proof was born obsolete, requiring more assumptions than an existing one
                self._proof = other._proof # use an old proof that does the job better
                kept_truths.append(other)
                born_obsolete = True
            else:
                # 'other' uses a different, non-redundant set of assumptions or
                # uses a subset of the assumptions but is unusable
                kept_truths.append(other)
        if not born_obsolete:
            if Judgment.theorem_being_proven is not None:
                if not Judgment.qed_in_progress and len(self.assumptions)==0 and self.expr == Judgment.theorem_being_proven.proven_truth.expr:
                    if not Judgment.has_been_proven:
                        Judgment.has_been_proven = True
                        print '%s has been proven. '%self.as_theorem_or_axiom().name, r'Now simply execute "%qed".'
            self._proof = new_proof
            kept_truths.append(self)
        # Remove the obsolete Judgments from the lookup_dict -- SHOULD ACTUALLY KEEP OLD PROOFS IN CASE ONE IS DISABLED -- TODO
        Judgment.lookup_dict[self.expr] = kept_truths
    """

    def _updateProof(self, new_proof):
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
                assert not meaning_data._proof.is_usable(), (
                        "should not update to an unusable new proof "
                        "if the old one was usable")
            return False  # did not change to something usable
        assert new_proof.is_usable(), (
                "Should not update with an unusable proof")

        self._checkIfReadyForQED(new_proof)

        if meaning_data._proof is None:
            # no previous dependents to update
            meaning_data._proof = new_proof
            return True  # new usable proof
        elif meaning_data._proof == new_proof:
            return False  # no change

        # swap out the old proof for the new proof in all dependencies
        meaning_data._proof._updateDependencies(new_proof)
        meaning_data._proof = new_proof  # set to the new proof

        return True

    def _checkIfReadyForQED(self, proof):
        if proof.is_usable() and proof.proven_truth == self:
            if Judgment.has_been_proven is not None:
                # check if we have a usable proof for the theorem being
                # proven
                if (not Judgment.qed_in_progress and 
                        len(self.assumptions) == 0 and 
                        (self.expr == 
                         Judgment.theorem_being_proven.proven_truth.expr)):
                    if not Judgment.has_been_proven:
                        Judgment.has_been_proven = True
                        print(
                            '%s has been proven. ' %
                            self.as_theorem_or_axiom().name,
                            r'Now simply execute "%qed".')
                        return True
        return False

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
        import inspect

        # called only if the attribute does not exist in Judgment 
        # directly
        if name == 'png':
            raise AttributeError(
                "Do not use the Expression version of the 'png' "
                "attribute.")
        attr = getattr(self.expr, name)

        if hasattr(attr, '__call__'):
            if name[:5] == 'with_':
                # 'with_...' methods change the style.  We want to
                # change the style and the return the judgment.
                def call_method_for_new_style(*args, **kwargs):
                    new_style_expr = attr.__call__(*args, **kwargs)
                    return self.with_matching_styles(new_style_expr, [])
                return call_method_for_new_style
            argspec = inspect.getfullargspec(attr)

            # TODO: Revisit this after we have switched to using
            # @prover or @equivalence_prover for all the methods.
            # This is more complicated than necessary for backward
            # compatibility.
            if ('assumptions' in argspec.args
                    or 'assumptions' in argspec.kwonlyargs
                    or  argspec.varkw == 'defaults_config'):
                # The attribute is a callable function with
                # 'assumptions' as an argument.
                # Automatically include the Judgment assumptions.

                # note, index zero is self.
                if 'assumptions' in argspec.args:
                    assumptions_idx = argspec.args.index('assumptions') - 1
                else:
                    assumptions_idx = None  # 'assumptions' is kwonly

                def call_method_with_judgment_assumptions(*args, **kwargs):
                    if (assumptions_idx is not None and
                            len(args) > assumptions_idx):
                        args = list(args)
                        assumptions = args[assumptions_idx]
                        assumptions = defaults.checked_assumptions(assumptions)
                        assumptions += self.assumptions
                        args[assumptions_idx] = \
                            defaults.checked_assumptions(assumptions)
                    else:
                        assumptions = kwargs.get('assumptions', USE_DEFAULTS)
                        assumptions = defaults.checked_assumptions(assumptions)
                        assumptions = tuple(assumptions) + self.assumptions
                        kwargs['assumptions'] = \
                            defaults.checked_assumptions(assumptions)
                    return attr.__call__(*args, **kwargs)
                return call_method_with_judgment_assumptions

        return attr

    def __dir__(self):
        '''
        The Judgment aquires the attributes of its Expression as well as 
        its own attributes.
        '''
        return sorted(set(dir(self.__class__) +
                          list(self.__dict__.keys()) + dir(self.expr)))

    def with_matching_styles(self, expr, assumptions):
        '''
        Return the Judgement expression with the styles matching
        those of the given expression and assumptions.
        '''
        new_style_expr = self.expr.with_matching_style(expr)
        # storing the assumptions in a trivial dictionary will be useful
        # for popping them out.
        assumptions_dict = {
            assumption: assumption for assumption in assumptions}
        new_style_assumptions = []
        for assumption in self.assumptions:
            if assumption in assumptions_dict:
                new_style_assumptions.append(
                        assumption.with_matching_style(
                                assumptions_dict.pop(assumption)))
            else:
                new_style_assumptions.append(assumption)
        new_style_judgment = \
            Judgment(new_style_expr, new_style_assumptions)
        if ((new_style_expr._style_id == self.expr._style_id) and
                all(new_style_assumption._style_id == old_assumption._style_id
                    for new_style_assumption, old_assumption in zip(
                            new_style_assumptions, self.assumptions))):
            # Nothing has changed.
            return self
            
        proof = new_style_judgment.proof()
        if proof is not None:
            # Update the style for the proof if there is one.
            new_style_proof = copy(proof)
            new_style_proof.proven_truth = self
            self._meaning_data._expr_proofs.insert(
                    new_style_proof)
            new_style_judgment._meaning_data._proof = \
                new_style_proof
        return new_style_judgment

    @staticmethod
    def find_judgment(expression, assumptions_set):
        '''
        Try to find a Judgment for this expression that applies to
        the given set of assumptions (its assumptions are a subset
        of the given assumptions).  Return None if there is no match.
        '''
        if expression not in Judgment.lookup_dict:
            return None
        truths = Judgment.lookup_dict[expression]
        suitable_truths = []
        for truth in truths:
            proof = truth.proof()
            if (proof is not None and proof.is_usable() and
                    truth.assumptions_set.issubset(assumptions_set)):
                suitable_truths.append(truth)
        if len(suitable_truths) == 0:
            return None  # no suitable truth
        # return one wih the shortest proof, and among those the fewest
        # assumptions
        best_judgment = min(suitable_truths,
                            key=lambda truth: (truth.proof().num_steps(),
                                               len(truth.assumptions)))
        # Make sure we get the desired style (and labels) for the
        # assumptions and 'truth'.
        # Although this looks vacuous, it will map an assumption of
        # any style to the assumption of the desired style.
        assumptions_with_style = {assumption: assumption for
                                  assumption in assumptions_set}
        if (best_judgment.expr._style_id != expression._style_id or
                any(assumption._style_id != assumptions_with_style[assumption]
                    for assumption in best_judgment.assumptions)):
            assumptions = [assumptions_with_style[assumption] for assumption in
                           best_judgment.assumptions]
            return best_judgment.with_matching_styles(expression,
                                                      assumptions)
        return best_judgment

    @staticmethod
    def forget_judgments():
        '''
        Forget all Judgment's and all Assumption proof objects.  This is
        used for demonstration purposes in the tutorial, but should not 
        generally be needed.
        '''
        from proof import Assumption
        Judgment.lookup_dict.clear()
        Assumption.all_assumptions.clear()

    def _checkedTruth(self, proof):
        proven_truth = proof.proven_truth
        if not proven_truth.is_usable():
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
        
        Returns the proven instantiated Judgment, or throws an exception
        if the proof fails.  For the proof to succeed, all conditions of
        eliminated Forall operations, after replacements are made, must
        be proven.  Furthermore, there may be additional requirements 
        when iterated parameters are instantiated (see Lambda.apply for
        details).  Automation mayb be used in attempting to prove these 
        requirements provided proveit.defaults.automation=True.
        '''
        from proveit import (Variable, Operation, Conditional, Lambda,
                             single_or_composite_expression,
                             ExprTuple, ExprRange, IndexedVar)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            get_param_var
        from proveit.logic import Forall
        from .proof import Theorem, Instantiation, ProofFailure
        
        if not self.is_usable():
            # If this Judgment is not usable, see if there is an alternate
            # under the set of assumptions that is usable.
            try:
                alternate = self.expr.prove(automation=False)
            except ProofFailure:
                self.raise_unusable_proof()
            return alternate.instantiate(repl_map)
        _proof = self.proof()
        if isinstance(_proof, Theorem):
            Theorem.all_used_theorems.add(_proof)

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
                        str(e))
                if key.num_entries() == 1:
                    key_entry = key.entries[0]
                    if (isinstance(key_entry, ExprRange) and
                            key_entry.start_index == key_entry.end_index
                            and isinstance(replacement, ExprTuple)
                            and replacement.is_single()):
                        # Special case of a singular range 
                        # (e.g., x_1, ..., x1) and singlular
                        # replacement.
                        processed_repl_map[key_entry.first()] = \
                            replacement.entries[0]
                    else:
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
        return self._checkedTruth(
            Instantiation(self,
                          num_forall_eliminations=num_forall_eliminations,
                          repl_map=processed_repl_map,
                          equiv_alt_expansions=equiv_alt_expansions,
                          assumptions=defaults.assumptions))

    def generalize(self, forall_var_or_vars_or_var_lists,
                   domain_lists=None, domain=None, conditions=tuple()):
        '''
        Performs a generalization derivation step.  Returns the
        proven generalized Judgment.  Can introduce any number of
        nested Forall operations to wrap the original statement,
        corresponding to the number of given forall_var_lists and 
        domains.  A single variable list or single variable and a single
        domain may be provided to introduce a single Forall wrapper.
        '''
        from proveit._core_.proof import Generalization
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            valid_params
        from proveit._core_.expression.composite.composite import \
            composite_expression
        from proveit.logic import InSet

        # Convert all forms of `forall_var_or_vars_or_var_lists` to
        # forall_var_lists, the most general form.  Start with the
        # default:
        forall_var_lists = forall_var_or_vars_or_var_lists
        try:
            forall_vars = composite_expression(forall_var_or_vars_or_var_lists)
            if valid_params(forall_vars):
                forall_var_lists = [forall_vars]
        except BaseException:
            pass  # don't change the default

        if not hasattr(forall_var_lists, '__len__'):
            raise ValueError("Must supply 'generalize' with a Variable, "
                             "list of Variables (or variable ranges), or "
                             "list of lists of Variables (or variable "
                             "ranges).")
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

        return self._checkedTruth(Generalization(self, forall_var_lists,
                                                 conditions))

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

    def eliminate(self, *skolem_constants, assumptions=USE_DEFAULTS):
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
        return Exists.eliminate(skolem_constants, self, assumptions)

    def evaluation(self, assumptions=USE_DEFAULTS):
        '''
        Calling evaluation on a Judgment results in deriving that its
        expression is equal to TRUE, under the assumptions of the 
        Judgment.
        '''
        from proveit.logic import evaluate_truth
        return evaluate_truth(self.expr, self.assumptions)

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
                Judgment.theorem_being_proven,
                unusuable_proof,
                'required to prove' +
                self.string(
                    perform_usability_check=False))

    def string(self, perform_usability_check=True):
        '''
        Display the turnstile notation to show that the judgment
        on the right derives from the set of assumptions on the left.
        '''
        from proveit import ExprTuple
        if perform_usability_check and not self.is_usable():
            self.raise_unusable_proof()
        if len(self.assumptions) > 0:
            assumptions_str = ExprTuple(
                *
                self.assumptions).formatted(
                'string',
                fence=False)
            return r'{' + assumptions_str + r'} |- ' + self.expr.string()
        return r'|- ' + self.expr.string()

    def latex(self, perform_usability_check=True):
        '''
        Display the turnstile notation to show that the judgment
        on the right derives from the set of assumptions on the left.
        '''
        from proveit import ExprTuple
        if perform_usability_check and not self.is_usable():
            self.raise_unusable_proof()
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
        if not self.is_usable():
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

    def inner_expr(self):
        '''
        Return an InnerExpr object to wrap the Judgment and
        access any inner sub-expression (including assumptions or
        inner expressions of assumptions) for the purpose of
        replacing the inner expression, changing its style,
        or relabeling variables.
        '''
        from .expression.inner_expr import InnerExpr
        return InnerExpr(self)


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
