"""
A Proof is a directed, acyclic graph (DAG) that represents the Prove-It
proof for a Judgment.  Each object represents a derivation step
(Assumption, ModusPonens, Deduction, Specialization,
or Generalization) and has references to other Judgments that
are directly required, each with its Proof.  In this way, the
Proof objects form a DAG.
"""

from collections import OrderedDict
import re
from proveit._core_.judgment import Judgment
from proveit._core_._unique_data import meaning_data, style_data
from .defaults import defaults
from .theory import Theory


class Proof:

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information in
        the Proof jurisdiction.
        '''
        Assumption.all_assumptions.clear()
        Theorem.all_theorems.clear()
        Theorem.all_used_theorems.clear()
        _ShowProof.show_proof_by_id.clear()

    def __init__(self, proven_truth, required_truths,
                 marked_required_truth_indices=None):
        '''
        # Uncomment to print useful debugging information when tracking side-effects.
        if not isinstance(self, Theorem) and not isinstance(self, Axiom):
            print "prove", proven_truth.expr
        '''

        assert isinstance(proven_truth, Judgment)
        for required_truth in required_truths:
            assert isinstance(required_truth, Judgment)
        # note: the contained Judgment and Proofs are subject to style changes
        # on a Proof instance basis.
        self.proven_truth = proven_truth
        self.required_truths = tuple(required_truths)
        if marked_required_truth_indices is None:
            self.marked_required_truth_indices = set()
        else:
            self.marked_required_truth_indices = \
                set(marked_required_truth_indices)
        for idx in self.marked_required_truth_indices:
            if not isinstance(idx, int) or idx < 0 or idx > len(
                    required_truths):
                raise ValueError("marked_required_truth_indices must be a set "
                                 "of integers indexing required_truths")

        # The meaning data is shared among Proofs with the same
        # structure disregarding style
        def meaning_hexid_fn(obj):
            if hasattr(obj, '_meaning_id'):
                return hex(obj._meaning_id)
            return hex(obj._establish_and_get_meaning_id())
        self._meaning_data = meaning_data(self._generate_unique_rep(
            meaning_hexid_fn))
        if not hasattr(self._meaning_data, 'required_proofs'):
            self._meaning_data.required_proofs = [
                required_truth.proof() for required_truth in required_truths]
            # meanng data of proofs that directly require this one
            self._meaning_data._dependents = set()

            # Is this a usable Proof?  An unusable proof occurs when 
            # trying to prove a Theorem that must explicitly presume 
            # Theorems that are not fully known in order to avoid 
            # circular logic.  They can also be manually introduced via
            # Proof.disable().
            # When unusable, this will point to the unusable theorem
            self._meaning_data._unusable_proof = None
            # being applied directly or indirectly.

        # The style data is shared among Proofs with the same structure and
        # style.
        self._style_data = style_data(
            self._generate_unique_rep(
                lambda obj: hex(
                    obj._style_id)))

        # Reference this unchanging data of the unique 'meaning' data.
        self._meaning_id = self._meaning_data._unique_id

        # Reference this data of the unique 'meaning' data, but note 
        # that these are subject to change (as proofs are disabled and 
        # as new dependencies are added).
        self.required_proofs = self._meaning_data.required_proofs
        self._dependents = self._meaning_data._dependents

        all_required_proofs = self.all_required_proofs()
        all_required_truths = {
            required_proof.proven_truth for required_proof in all_required_proofs if required_proof is not self}
        original_proof = self.proven_truth not in all_required_truths

        if original_proof:
            # As long as this is not a useless self-dependent proof (a 
            # proof that depends upon a different proof of the same
            # truth which should never actually get used), track the 
            # dependencies of required proofs so they can be updated 
            # appropriately if there are changes due to proof disabling.
            for required_proof in self.required_proofs:
                required_proof._dependents.add(self)

        if not hasattr(self._meaning_data, 'num_steps'):
            # determine the number of unique steps required for this proof
            self._meaning_data.num_steps = len(all_required_proofs)

        self._style_id = self._style_data._unique_id

        if not original_proof:
            self._meaning_data._unusable_proof = self  # not usable because it is not useful
            assert proven_truth.proof() is not None, "There should have been an 'original' proof"
            return

        requiring_unusable_proof = False
        for required_proof in self.required_proofs:
            if required_proof.is_usable():
                # Required proof is a theorem being used.
                if isinstance(required_proof, Theorem):
                    Theorem.all_used_theorems.add(required_proof)
            else:
                # Mark proofs as unusable when using an "unusable" theorem
                # directly or indirectly.  Theorems are marked as unusable
                # when a proof for some Theorem is being generated as a
                # means to avoid circular logic.
                self._meaning_data._unusable_proof = required_proof._meaning_data._unusable_proof
                # Raise an UnusableProof expection below (after calling _recordBestProof
                # to indicate the proof is unusable).
                requiring_unusable_proof = True
                break  # it only take one

        # if it is a Theorem, set its "usability", avoiding circular logic
        if self.is_usable():
            self._mark_usability()
        # This new proof may be the first proof, make an old one 
        # obselete, or be born obsolete itself.
        #had_previous_proof = (proven_truth.proof() is not None and proven_truth.is_usable())
        proven_truth._add_proof(self)
        if requiring_unusable_proof:
            # Raise an UnusableProof exception when an attempt is made
            # to use an "unusable" theorem directly or indirectly.
            raise UnusableProof(
                Judgment.theorem_being_proven,
                self._meaning_data._unusable_proof)
        if proven_truth.proof() == self and self.is_usable(): 
            # Don't bother with side effects if this proof was born 
            # obsolete or unusable.  May derive any side-effects that 
            # are obvious consequences arising from this truth
            # (if it has not already been processed):
            with defaults.temporary() as temp_defaults:
                # Disable auto-simplification and clear the
                # 'replacements' while deriving side-effects.
                temp_defaults.auto_simplify = False
                if len(defaults.replacements) > 0:
                    temp_defaults.replacements = []
                proven_truth.derive_side_effects()

    def _update_dependencies(self, newproof):
        '''
        Swap out this oldproof for the newproof in all dependents and 
        update their num_steps and usability status.
        '''
        newproof._dependents.clear()
        oldproof = self

        for dependent in oldproof._dependents:
            revised_dependent = False
            for i in range(len(dependent.required_proofs)):
                if dependent.required_proofs[i] == oldproof:
                    dependent.required_proofs[i] = newproof
                    revised_dependent = True
            assert revised_dependent, (
                    "Dependency/requirement relationship not mutual: "
                    "a dependent, proving %s, of the proof of, %s, "
                    "does not require the particular proof mutually."
                    %(dependent.proven_truth, oldproof.proven_truth))
            newproof._dependents.add(dependent)
            dependent._mark_num_steps_as_unknown()
            if all(required_proof.is_usable()
                   for required_proof in dependent.required_proofs):
                dependent._meaning_data._unusable_proof = None  # it is usable again
                dependent.proven_truth._add_proof(
                    dependent)  # add it back as an option
        # Nothing should depend upon the old proof any longer.
        oldproof._dependents.clear()        

    def _mark_usability(self, set_to_disable=None):
        pass  # overloaded for the Theorem type Proof

    def _generate_unique_rep(self, object_rep_fn):
        '''
        Generate a unique representation string using the given function
        to obtain representations of other referenced Prove-It objects.
        '''
        # Internally, for self._meaning_rep and self._style_rep, we will
        # use self.required_truths in the unique representation and
        # the proofs are subject to change (if anything is disabled).
        # For external storage (see _theory_storage.py), we will use
        # self.required_proofs, locking the mapping from KnonwTruths of
        # self.required_truths to Proofs.
        required_objs = (self.required_proofs
                         if hasattr(self, 'required_proofs')
                         else self.required_truths)
        required_obj_marks = [('*' if k in self.marked_required_truth_indices
                               else '') for k in range(len(required_objs))]
        required_objs_str = ','.join(object_rep_fn(obj) + mark for obj, mark
                                     in zip(required_objs, required_obj_marks))
        return (self._generate_step_info(object_rep_fn) +
                '[%s];[%s]'
                % (object_rep_fn(self.proven_truth), required_objs_str))

    def _generate_step_info(self, object_rep_fn):
        '''
        Generate information about this proof step.
        Overridden by Specialization which also needs to including the 
        mapping information and uses the given function to obtain 
        representations of sub-Object.
        '''
        return self.step_type() + ':'

    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of
        representations of Prove-It objects that are referenced.
        '''
        # Skip the step type (and axiom/theorem name if it is either of those types)
        # which is in the beginning and followed by a ':'
        remaining = unique_rep.split(':', 1)[-1]
        # Everything else coming between the punctuation,
        # ';', ':', ',', '{', '}', '[', ']', is a represented object.
        obj_ids = re.split(r"\{|\[|,|:|;|\]|\}", remaining)
        # Remove the '*' marks, marking the "equality replacement
        # requirements".
        return [obj_id.rstrip('*') for obj_id in obj_ids if len(obj_id) > 0]

    @staticmethod
    def _extractKindAndName(unique_rep):
        '''
        Given a 'unique_rep' for an Axiom or Theorem, return
        'axiom' or 'theorem' and its full name.  Raise a ValueError
        if it isn't an Axiom or Theorem.
        '''
        if unique_rep[:6] != 'Proof:':
            raise ValueError("Invalid 'unique_rep' for Proof: %s" % unique_rep)
        step_info, remaining = unique_rep[6:].split(':', 1)
        kind, full_name = step_info.split('_', 1)
        return (kind, full_name)

    @staticmethod
    def _showProof(theory, folder, proof_id, unique_rep):
        '''
        Given a unique representation string, returns a _ShowProof
        object that mocks up a stored proof for the purposes of
        displaying it.
        '''
        # Skip the step type (and axiom/theorem name if it is either of
        # those types) which is in the beginning and followed by a ':'
        if unique_rep[:6] != 'Proof:':
            raise ValueError("Invalid 'unique_rep' for Proof: %s" % unique_rep)
        step_info, remaining = unique_rep[6:].split(':', 1)
        # extract groups each wrapped in braces, either '{..}' or '[..]'
        group_strs = []
        while len(remaining) > 0:
            if remaining[0] == ';':
                remaining = remaining[1:]
            start_brace = remaining[0]
            if start_brace not in ('{', '['):
                raise ValueError(
                    "Invalid starting brace of 'unique_rep': %s" % remaining[0])
            end_brace = '}' if start_brace == '{' else ']'
            remaining = remaining[1:]
            group_str, remaining = remaining.split(end_brace, 1)
            group_strs.append(group_str)
        # The id's of each group come between the punctuation:
        # ';', ':', ','.
        groups = []
        for group_str in group_strs:
            obj_ids = re.split(",|:|;", group_str)
            groups.append([obj_id for obj_id in obj_ids if len(obj_id) > 0])
        if proof_id in _ShowProof.show_proof_by_id:
            return _ShowProof.show_proof_by_id[proof_id]
        return _ShowProof(theory, folder, proof_id, step_info, groups)

    def is_usable(self):
        '''
        Returns True iff this Proof is usable.  A Proof may be unusable
        because it was manually disabled or because it is not being presumed
        while trying to prove a Theorem (other Theorems must be explicitly
        presumed in order to avoid circular logic).
        '''
        return self._meaning_data._unusable_proof is None

    def disable(self):
        '''
        Disable the use of this Proof and any of its dependents
        that don't have an alternate proof that doesn't rely
        on this one.
        '''
        Proof._disable_all([self])
    
    @staticmethod
    def _disable_all(to_disable):
        '''
        Disable all of the Theorems in 'to_disable', disabling
        their dependencies or revising them to use alternate
        proofs if available.
        '''
        # Disable in an order sorted according to the number
        # of steps so that dependents are visited after
        # everything they depend upon and we avoid revising
        # and discarding proofs multiple times.
        import heapq
        # The 'sources' are the originally disabled proofs
        # that may propagate to dependents.
        dep_id_to_dep_and_source = dict()
        for proof in to_disable:
            dep_id_to_dep_and_source[id(proof)] = (proof, proof)
        dependents_by_nsteps = [(proof.num_steps(), id(proof)) 
                                for proof in to_disable
                                if proof.is_usable()]

        # In the first pass, disable the 'to_disable' set and
        # their direct/indirect dependence in a monotonic order
        # (avoiding repeats).
        next_pass_dependents_by_nsteps = []
        heapq.heapify(dependents_by_nsteps)
        while len(dependents_by_nsteps) > 0:
            _n, dependent_id = heapq.heappop(dependents_by_nsteps)
            next_pass_dependents_by_nsteps.append((_n, dependent_id))
            dependent, source = \
                dep_id_to_dep_and_source[dependent_id]
            is_defunct = (dependent.proven_truth.proof() == dependent)
            dependent._meaning_data._unusable_proof = source
            dependent.proven_truth._discard_proof(dependent)
            # Make the number of steps as unknown as we go up through
            # the dependents.
            dependent._meaning_data.num_steps = None
            if not is_defunct:
                # A different proof was active, so we don't have
                # worry about its dependents.
                continue
            # Push sub-dependents onto the heap.
            for _dependent in dependent._dependents:
                if _dependent.is_usable():
                    dep_id_to_dep_and_source[id(_dependent)] = (
                        _dependent, source)
                    heapq.heappush(dependents_by_nsteps,
                                   (_dependent.num_steps(),
                                    id(_dependent)))

        # In a second pass, see if there are alternative proofs.
        # Doing this in a separate pass avoids making revisions
        # that generate circular dependencies.
        dependents_by_nsteps = next_pass_dependents_by_nsteps
        heapq.heapify(dependents_by_nsteps)
        while len(dependents_by_nsteps) > 0:
            _n, dependent_id = heapq.heappop(dependents_by_nsteps)
            dependent, _ = dep_id_to_dep_and_source[dependent_id]
            if dependent.is_usable():
                # Already enabled, so we can skip it.
                continue
            is_defunct = (dependent.proven_truth.proof() == dependent)
            if not is_defunct:
                # A different proof was active, so we don't have
                # to revise it.
                continue
            # Use an alternate proof if available.
            dependent.proven_truth._revise_proof()

    def __eq__(self, other):
        if isinstance(other, Proof):
            return self._meaning_id == other._meaning_id
        else:
            return False  # other must be an Expression to be equal to self

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._meaning_id

    def num_steps(self):
        '''
        Return the number of unique steps in the proof.
        '''
        if self._meaning_data.num_steps is None:
            # Compute the number of steps as needed.
            self._meaning_data.num_steps = len(self.all_required_proofs())
        return self._meaning_data.num_steps

    def _mark_num_steps_as_unknown(self):
        '''
        Mark the number of steps of this proof, and all
        of its dependents, as unknown to force it to
        be recomputed if it is needed.
        '''
        to_process = [self]
        while len(to_process) > 0:
            proof = to_process.pop()
            if proof._meaning_data.num_steps is not None:
                proof._meaning_data.num_steps = None
                to_process.extend(proof._dependents)

    def used_axioms(self):
        '''
        Returns the set of names of axioms that are used directly (not via other theorems) in this proof.
        '''
        return set().union(*[required_proof.used_axioms()
                             for required_proof in self.required_proofs])

    def used_theorems(self):
        '''
        Returns the set of names of axioms that are used directly (not via other theorems) in this proof.
        '''
        return set().union(*[required_proof.used_theorems()
                             for required_proof in self.required_proofs])

    def assumptions(self):
        return self.proven_truth.assumptions

    def get_link(self):
        '''
        Return the link to the proof notebook.  It the Proof is a
        Theorem or Axiom, this is overridden to return the link to
        the theorem/axiom definition.
        '''
        theory = Theory()
        return theory.proof_notebook(self)

    def __setattr__(self, attr, value):
        '''
        Proofs should be read-only objects except for changing
        the proven_truth to another with the same meaning (but
        possibly different style).  Attributes may be added, 
        however; for example, the 'png' attribute which will be added 
        whenever it is generated).
        '''
        if hasattr(self, attr):
            # It is okay to change to proven_truth to another one
            # with the same meaning but possibly different style.
            # But otherwise, we want to treat attributes as read only.
            if attr != 'proven_truth' or value != self.__dict__[attr]:
                raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value

    def enumerated_proof_steps(self):
        '''
        Returns a list of Proof objects that includes self and
        all of its direct and indirect requirements.  Duplicates
        will not be included, but they will be presented in an
        order which makes it clear that the dependencies are
        acyclic by making sure requirements come after dependents.
        '''
        from ._dependency_graph import ordered_dependency_nodes
        return ordered_dependency_nodes(
            self, lambda proof: proof.required_proofs)

    def all_required_proofs(self, all_requirements_chain = None):
        '''
        Returns the set of directly or indirectly required proofs.
        '''
        sub_proof_sets = [required_proof.all_required_proofs(all_requirements_chain)
                          for required_proof in self.required_proofs]
        return set([self]).union(*sub_proof_sets)

    def _repr_html_(self):
        if not defaults.display_latex:
            return None  # No LaTeX display at this time.
        proof_steps = self.enumerated_proof_steps()
        html = '<table><tr><th>&nbsp;</th><th>step type</th><th>requirements</th><th>statement</th></tr>\n'
        first_requirements = None
        # If this is a _ShowProof object, _style_id will be a str.
        proof_id = self._style_id if isinstance(self._style_id, str) \
            else hex(self._style_id)

        # For convenience, we will reference all of the first (top-level)
        # requirements at the top even if it is a simple reference.
        amended_proof_steps = []
        for k, proof in enumerate(proof_steps):
            if k == 0:
                first_requirements = iter(proof.required_proofs)
            else:
                while first_requirements is not None:
                    try:
                        req = next(first_requirements)
                        if req == proof:
                            break
                        # Just reference a later step.
                        amended_proof_steps.append(_ProofReference(req))
                    except StopIteration:
                        # Done with the first requirements:
                        first_requirements = None
            amended_proof_steps.append(proof)
        proof_steps = amended_proof_steps

        any_marked = False

        def req_link(proof, req_idx, n):
            nonlocal any_marked
            is_marked = (req_idx in proof.marked_required_truth_indices)
            if is_marked:
                any_marked = True
            mark_str = r'<sup>*</sup>' if is_marked else ''
            return ('<a href="#%s_step%d">%d</a>%s'
                    % (proof_id, n, n, mark_str))
        proof_num_map = {proof: k for k, proof in enumerate(proof_steps)}
        for k, proof in enumerate(proof_steps):
            html += '<tr><td><a name="%s_step%d">%d</a></td>' % (
                proof_id, k, k)
            if k == 0:
                # The first (top-level) proof has requirements at the
                # top by design (though some of these may be references to
                # later steps).
                required_proof_nums = \
                    ', '.join(req_link(proof, k, k + 1) for k, _
                              in enumerate(proof.required_proofs))
            else:
                required_proof_nums = \
                    ', '.join(req_link(proof, k, proof_num_map[required_proof])
                              for k, required_proof
                              in enumerate(proof.required_proofs))
            html += '<td>%s</td><td>%s</td>' % (
                proof.step_type(), required_proof_nums)
            html += '<td>%s</td>' % proof.proven_truth._repr_html_()
            html += '</tr>\n'
            if proof.step_type() == 'instantiation':
                html += '<tr><td>&nbsp;</td><td colspan=4 style="text-align:left">' + \
                    proof._mapping('HTML') + '</td></tr>'
            if proof.step_type() in {'axiom', 'theorem', 'conjecture'}:
                html += '<tr><td>&nbsp;</td><td colspan=4 style-"text-align:left">'
                html += '<a class="ProveItLink" href="%s">' % proof.get_link() + str(proof.theory) + \
                    '.' + proof.name + '</a>'
                html += '</td></tr>'
        if any_marked:
            html += ('<tr><td colspan=4 style="text-align:left">'
                     r'<sup>*</sup>equality replacement requirements'
                     '</td></tr>')
        html += '</table>'
        return html

    def __repr__(self):
        proof_steps = self.enumerated_proof_steps()
        proof_num_map = {proof: k for k, proof in enumerate(proof_steps)}
        any_marked = False

        def req_ref(proof, req_idx):
            global any_marked
            req = proof.required_proofs[req_idx]
            is_marked = (req_idx in proof.marked_required_truth_indices)
            if is_marked:
                any_marked = True
            mark_str = r'*' if is_marked else ''
            return ('%d%s' % (proof_num_map[req], mark_str))
        out_str = '\tstep type\trequirements\tstatement\n'
        for k, proof in enumerate(proof_steps):
            out_str += str(k) + '\t'
            required_proof_refs = \
                ', '.join(req_ref(proof, k) for k
                          in range(len(proof.required_proofs)))
            out_str += proof.step_type() + '\t' + required_proof_refs + '\t'
            out_str += proof.proven_truth.string(perform_usability_check=False)
            out_str += '\n'
            if proof.step_type() == 'instantiation':
                out_str += '\t' + proof._mapping('str') + '\n'
            if proof.step_type() in ('axiom', 'theorem', 'conjecture'):
                out_str += '\t' + str(proof.theory) + '.' + proof.name + '\n'
        if any_marked:
            out_str += ('* equality replacement requirements\n')
        return out_str


class _ProofReference:
    '''
    May be used as a dummy Proof in Proof._repr_html_ in order to refer
    to a later proof step while keeping the "first" (top-level)
    requirements at the top.
    '''

    def __init__(self, ref):
        self.required_proofs = [ref]
        self.proven_truth = ref.proven_truth
        self.marked_required_truth_indices = set()  # nothing marked

    def step_type(self):
        # only used in the HTML version
        return '<i>reference</i>'


class Assumption(Proof):
    # Map expressions to corresponding assumption objects.
    all_assumptions = dict()

    def __init__(self, expr, assumptions=None):
        from proveit import ExprRange
        assert expr not in Assumption.all_assumptions, \
            ("Do not create an Assumption object directly; "
             "use Assumption.make_assumption instead.")
        assumptions = defaults.checked_assumptions(assumptions)
        if expr not in assumptions:
            # An Assumption proof must assume itself;
            # that's what it does.
            assumptions = assumptions + (expr,)
        prev_default_assumptions = defaults.assumptions
        # These assumptions will be used for deriving any side-effects
        defaults.assumptions = assumptions
        # The assumed truth from a ranges of assumptions
        # must be wrapped in a conjunction (And).
        if isinstance(expr, ExprRange):
            from proveit.logic import And
            assumed_truth = And(expr)
        else:
            assumed_truth = expr
        try:
            Proof.__init__(self, Judgment(assumed_truth, {expr}), [])
        finally:
            # Restore the original default assumptions
            defaults.assumptions = prev_default_assumptions
        Assumption.all_assumptions[expr] = self

    @staticmethod
    def make_assumption(expr, assumptions):
        '''
        Return an Assumption object, only creating it if it doesn't
        already exist.  assumptions must already be 'checked' and in
        tuple form.
        '''
        if expr in Assumption.all_assumptions:
            preexisting = Assumption.all_assumptions[expr]
            # The Assumption object exists already, but it's
            # side-effects may not have been derived yet under the
            # given assumptions.
            # This can happen when automation is temporarily disabled or
            # when assumptions change.
            with defaults.temporary() as temp_defaults:
                temp_defaults.assumptions = assumptions
                preexisting.proven_truth.derive_side_effects()
            return preexisting
        return Assumption(expr, assumptions)

    def step_type(self):
        return 'assumption'


class Axiom(Proof):
    def __init__(self, expr, theory, name):
        if not isinstance(theory, Theory):
            raise ValueError("An axiom 'theory' must be a Theory object")
        if not isinstance(name, str):
            raise ValueError("An axiom 'name' must be a string")
        self.theory = theory
        self.name = name
        Proof.__init__(self, Judgment(expr, frozenset()), [])

    def _generate_step_info(self, object_rep_fn):
        return self.step_type() + '_' + str(self) + ':'

    def step_type(self):
        return 'axiom'

    def _storedAxiom(self):
        from ._theory_storage import StoredAxiom
        return StoredAxiom(self.theory, self.name)

    def get_link(self):
        '''
        Return the HTML link to the axiom definition.
        '''
        return self._storedAxiom().get_def_link()

    def used_axioms(self):
        return {self}

    def direct_dependents(self):
        '''
        Returns the theorems that depend directly upon this axioms.
        '''
        return self._storedAxiom().read_dependent_theorems()

    def all_dependents(self):
        return self._storedAxiom().all_dependents()

    def __str__(self):
        return self.theory.name + '.' + self.name


class Theorem(Proof):
    all_theorems = []
    all_used_theorems = set()

    def __init__(self, expr, theory, name):
        if not isinstance(theory, Theory):
            raise ValueError("A theorem 'package' must be a Theory object")
        if not isinstance(name, str):
            raise ValueError("A theorem 'name' must be a string")
        self.theory = theory
        self.name = name
        # keep track of proofs that may be used to prove the theorem
        # before 'begin_proof' is called so we will have the proof handy.
        self._possibleProofs = []
        # Note that _mark_usability will be called within Proof.__init__
        Proof.__init__(self, Judgment(expr, frozenset()), [])
        Theorem.all_theorems.append(self)

    def _generate_step_info(self, object_rep_fn):
        # For these purposes, we should use 'theorem' even if the
        # status is 'conjecture'.
        return 'theorem_' + str(self) + ':'

    def step_type(self):
        if self.is_conjecture():
            return 'conjecture'
        return 'theorem'

    def used_theorems(self):
        return {self}

    def __str__(self):
        return self.theory.name + '.' + self.name

    def __repr__(self):
        return self.theory.name + '.' + self.name

    def theorem_name_and_containing_theories(self):
        '''
        Yields all containing theory names and the full theorem name.
        '''
        s = str(self)
        hierarchy = s.split('.')
        for k in range(1, len(hierarchy)):
            yield '.'.join(hierarchy[:k])
        yield s

    @staticmethod
    def update_usability():
        set_to_disable = set()
        for theorem in Theorem.all_theorems:
            theorem._mark_usability(set_to_disable)
        Proof._disable_all(set_to_disable)

    def _stored_theorem(self):
        from ._theory_storage import StoredTheorem
        return StoredTheorem(self.theory, self.name)

    def get_link(self):
        '''
        Return the HTML link to the theorem proof file.
        '''
        return self._stored_theorem().get_proof_link()

    """
    def record_presumed_theories(self, presumed_theory_names):
        '''
        Record information about what other theories are
        presumed in the proof of this theorem.
        '''
        self._stored_theorem().record_presumed_theories(presumed_theory_names)

    def presumed_theories(self):
        '''
        Return the list of presumed theories.
        '''
        return self._stored_theorem().presumed_theories()

    def record_presumed_theorems(self, explicitly_presumed_theorem_names):
        '''
        Record information about what othere theorems are
        presumed in the proof of this theorem.
        '''
        self._stored_theorem().record_presumed_theorems(explicitly_presumed_theorem_names)

    def explicitly_presumed_theorem_names(self):
        '''
        Return the list of names of explicitly presumed theorems.
        (indicated after 'presuming' in the proof notebook).
        '''
        return self._stored_theorem().explicitly_presumed_theorem_names()

    def get_all_presumed_theorem_names(self):
        '''
        Return the set of full names of presumed theorems that are
        directly or indirectly presumed by the theorem of the given name
        in this theory.
        '''
        return self._stored_theorem().get_all_presumed_theorem_names()
    """

    def get_presumptions_and_exclusions(self):
        '''
        Return the set of theorems and theories that are explicitly
        presumed by this theorem, and a set of exclusions (e.g.,
        you could presume the proveit.logic theory but exclude
        proveit.logic.equality).
        '''
        return self._stored_theorem().get_presumptions_and_exclusions()

    def _recordProof(self, proof):
        '''
        Record the given proof as the proof of this theorem.  Updates
        dependency links (used_axioms.txt, used_theorems.txt, and used_by.txt files)
        and proven dependency indicators (various proven_theorems.txt files
        for theorems that depend upon the one being proven) appropriately.
        '''
        self._stored_theorem()._recordProof(proof)

    def remove_proof(self):
        '''
        Remove the proof for the given theorem and all obsolete dependency
        links.
        '''
        self._stored_theorem().remove_proof()

    def has_proof(self):
        '''
        Returns true if and only if this theorem has a recorded proof.
        '''
        return self._stored_theorem().has_proof()

    def is_fully_proven(self):
        '''
        Returns true if and only if this theorem is fully proven
        (it has a recorded proof and all dependent theorems are fully
        proven, all the way to axioms which don't require proofs).
        '''
        return self._stored_theorem().is_complete()

    def is_conjecture(self):
        '''
        A "Theorem" that is not fully proven is a "conjecture".
        '''
        return not self.is_fully_proven()

    def all_requirements(self):
        '''
        Returns the set of axioms that are required (directly or indirectly)
        by the theorem.  Also, if the given theorem is not completely proven,
        return the set of unproven theorems that are required (directly or
        indirectly).  Returns this axiom set and theorem set as a tuple.
        '''
        return self._stored_theorem().all_requirements()

    def all_used_or_presumed_theorem_names(self, names=None):
        '''
        Returns the set of theorems used to prove the theorem or to be presumed
        in the proof of the theorem, directly or indirectly (i.e., applied
        recursively); this theorem itself is also included.
        If a set of 'names' is provided, this will add the 
        names to that set and skip over anything that is already in the set, 
        making the assumption that its dependents have already been
        included (e.g., if the same set is used in multiple calls to this
        method for different theorems).
        '''
        return self._stored_theorem().all_used_or_presumed_theorem_names(names)

    def direct_dependents(self):
        '''
        Returns the theorems that depend directly upon this axioms.
        '''
        return self._stored_theorem().read_dependent_theorems()

    def all_dependents(self):
        '''
        Returns the set of theorems that are known to depend upon this
        theorem directly or indirectly.
        '''
        return self._stored_theorem().all_dependents()

    def _mark_usability(self, set_to_disable=None):
        '''
        Determine whether or not we need to disable the
        theorem -- if some theorem is being proven and this
        theorem is not presumed or is an alternate proof for the
        same theorem.  Also, if it is presumed, ensure the logic
        is not circular.  Generally, this is preventing circular
        logic.  This applies when a proof has begun
        (see Judgment.begin_proof in judgment.py).
        When Judgment.theorem_being_proven is None, all Theorems are 
        allowed.  Otherwise only Theorems named in the 
        Judgment.presuming_theorem_names set
        or contained within any of the Judgment.presuming_theories
        (i.e., theory) are allowed.
        
        If set_to_disable is provided, instead of actively disabling
        proofs, collect them in a set to be disabled more efficiently.
        '''
        #from proveit.certify import is_fully_proven
        if Judgment.theorem_being_proven is None:
            # Nothing being proven, so all Theorems are usable
            self._meaning_data._unusable_proof = None
            return
        legitimately_presumed = False
        stored_theorem = self._stored_theorem()
        theorem_being_proven_str = Judgment.theorem_being_proven_str
        presumed_theorems_and_dependencies = \
            Judgment.presumed_theorems_and_dependencies
        if self.proven_truth == Judgment.theorem_being_proven.proven_truth:
            # Note that two differently-named theorems for the same thing may exists in
            # order to show an alternate proof.  In that case, we want to disable
            # the other alternates as well so we will be sure to generate the
            # new proof.
            if set_to_disable is None:
                self.disable()
            else:
                set_to_disable.add(self)
            return
        else:
            name_and_containing_theories = list(
                self.theorem_name_and_containing_theories())
            specifically_presumed = (str(self) in 
                                     Judgment.presumed_theorems_and_theories)
            if specifically_presumed:
                presumed = True
            else:
                exclusions = Judgment.presuming_theorem_and_theory_exclusions
                if exclusions.isdisjoint(name_and_containing_theories):
                    presumptions = Judgment.presumed_theorems_and_theories
                    presumed = not presumptions.isdisjoint(
                        name_and_containing_theories)
                else:
                    presumed = False
            if presumed:
                # This Theorem is being presumed specifically, or a theory
                # in which it is contained is presumed.  We'll check its
                # dependencies to avoid circuit logic.  If there is a
                # circular dependence, we'll either raise a CircularLogic
                # exception if the theorm was presumed specifically or
                # simply disregard it if it was presumed as part of a
                # theory.
                stored_theorem.all_used_or_presumed_theorem_names(
                    presumed_theorems_and_dependencies)
                if theorem_being_proven_str in presumed_theorems_and_dependencies:
                    # Theorem-specific presumption or dependency is
                    # mutual.  Raise a CircularLogic error.
                    raise CircularLogic(
                        Judgment.theorem_being_proven, self,
                        implicitly_presumed = not specifically_presumed)
                else:
                    legitimately_presumed = True
        if not legitimately_presumed:
            # This Theorem is not usable during the proof (if it is needed, it must be
            # presumed or fully proven).  Propagate this fact to all
            # dependents.
            if set_to_disable is None:
                self.disable()
            else:
                set_to_disable.add(self)


def _checkImplication(implication_expr, antecedent_expr, consequent_expr):
    '''
    Make sure the implication_expr is a proper implication with
    antecedent_expr as the antecedent and consequent_expr as the consequent.
    '''
    from proveit.logic import Implies
    from proveit._core_.expression.composite import is_double
    assert isinstance(
        implication_expr, Implies), 'The result of deduction must be an Implies operation'
    assert is_double(implication_expr.operands), (
            'Implications are expected to have two operands')
    assert antecedent_expr == implication_expr.operands[
        0], 'The result of deduction must be an Implies operation with the proper antecedent'
    assert consequent_expr == implication_expr.operands[
        1], 'The result of deduction must be an Implies operation with the proper consequent'


class ModusPonens(Proof):
    def __init__(self, implication_expr, assumptions=None):
        from proveit.logic import Implies
        from proveit._core_.expression.composite import is_double
        assumptions = defaults.checked_assumptions(assumptions)
        prev_default_assumptions = defaults.assumptions
        # these assumptions will be used for deriving any side-effects
        defaults.assumptions = assumptions
        try:
            # obtain the implication and antecedent Judgments
            assert (isinstance(implication_expr, Implies) and 
                    is_double(implication_expr.operands)), (
                            'The implication of a modus ponens proof must '
                            'refer to an Implies expression with two operands')
            try:
                # Must prove the implication under the given assumptions.
                implication_truth = implication_expr.prove(
                        assumptions=assumptions)
            except ProofFailure:
                raise ModusPonensFailure(
                    implication_expr.operands[1],
                    assumptions,
                    'Implication, %s, is not proven' %
                    str(implication_expr))
            try:
                # Must prove the antecedent under the given assumptions.
                antecedent_truth = implication_expr.operands[0].prove(
                    assumptions=assumptions)
            except ProofFailure:
                raise ModusPonensFailure(
                    implication_expr.operands[1],
                    assumptions,
                    'Antecedent of %s is not proven' %
                    str(implication_expr))
            # remove any unnecessary assumptions (but keep the order that was
            # provided)
            assumptions_set = implication_truth.assumptions_set | antecedent_truth.assumptions_set
            assumptions = [
                assumption for assumption in assumptions if assumption in assumptions_set]
            # we have what we need; set up the ModusPonens Proof
            consequent_truth = Judgment(
                implication_expr.operands[1], assumptions)
            _checkImplication(
                implication_truth.expr,
                antecedent_truth.expr,
                consequent_truth.expr)
            self.implication_truth = implication_truth
            self.antecedent_truth = antecedent_truth
            Proof.__init__(
                self, consequent_truth, [
                    self.implication_truth, self.antecedent_truth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def step_type(self):
        return 'modus ponens'


class Deduction(Proof):
    def __init__(self, consequent_truth, antecedent_expr):
        from proveit import ExprRange
        from proveit.logic import Implies, And
        if isinstance(antecedent_expr, ExprRange):
            # Assumption ranges must be transformed to a
            # conjunction form on the other side.
            elim_assumption = antecedent_expr
            antecedent_expr = And(antecedent_expr)
        else:
            elim_assumption = antecedent_expr
        assumptions = [assumption for assumption in consequent_truth.assumptions
                       if assumption != elim_assumption]
        prev_default_assumptions = defaults.assumptions
        # These assumptions will be used for deriving any side-effects
        defaults.assumptions = assumptions
        try:
            implication_expr = Implies(antecedent_expr, consequent_truth.expr)
            implication_truth = Judgment(implication_expr, assumptions)
            self.consequent_truth = consequent_truth
            Proof.__init__(self, implication_truth, [self.consequent_truth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def step_type(self):
        return 'deduction'


class Instantiation(Proof):
    def __init__(self, orig_judgment, num_forall_eliminations,
                 repl_map, equiv_alt_expansions, assumptions):
        '''
        Create the instantiation proof step that eliminates some number
        of nested Forall operations and simultaneously replaces 
        Variables with Expressions according to the replacement map 
        (repl_map).  A Variable that is a parameter variable of an 
        internal Lambda expression may only be relabeled; it will not 
        be replaced with a non-Variable expression within the scope of
        the Lambda expression.

        See Expression.substituted for details regarding the replacement 
        rules.
        '''
        from proveit import (Variable, Function, Lambda, ExprTuple, 
                             ExprRange, IndexedVar)
        from proveit._core_.expression.expr import contained_parameter_vars
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (get_param_var, valid_params, LambdaApplicationError)
        from proveit._core_.expression.label.var import safe_dummy_var
        
        # Determine the set of variables that will be instantiated
        # via eliminated foralls.
        instantiating_vars = Instantiation._get_nested_param_vars(
                orig_judgment.expr, num_forall_eliminations)
        orig_contained_param_vars = contained_parameter_vars(orig_judgment)

        # Map parameters to the number of corresponding operand
        # entries to speed matching parameters and operands and
        # disambiguate parameter ownership of emtpy ranges of
        # operands.
        param_to_num_operand_entries = dict()
        
        # Prepare the 'relabel_params' for basic relabeling that 
        # can apply to both sides of the turnstile.
        relabel_params = []
        relabel_param_replacements = []
        for key, repl in repl_map.items():
            if isinstance(key, ExprTuple):
                key_var = get_param_var(key[0])
            else:
                key_var = get_param_var(key)
            if key_var in instantiating_vars:
                # If it is a variable being instantiated,
                # it is not a relabeling param.
                continue
            elif key_var not in orig_contained_param_vars:
                raise ValueError("'%s' is not one of the variables that may "
                                 "be instantiated or relabeled in %s."
                                 %(key, orig_judgment))                
            if ((isinstance(key, Variable) or isinstance(key, IndexedVar))
                    and (isinstance(repl, Variable)
                         or (isinstance(repl, ExprTuple) 
                             and valid_params(repl)))):
                _param = key
                relabel_param_replacements.append(repl)
                param_to_num_operand_entries[_param] = 1
            elif (isinstance(key, ExprTuple)
                    and key.num_entries()==1
                    and valid_params(key)
                    and isinstance(repl, ExprTuple)
                    and valid_params(repl)):
                _param = key.entries[0]
                relabel_param_replacements.extend(repl.entries)
                param_to_num_operand_entries[_param] = repl.num_entries()
            else:
                raise ValueError("'%s' is not a proper relabeling for '%s' "
                                 "and '%s' is not properly instantiated in %s."
                                 %(repl, key, key_var, orig_judgment))
            relabel_params.append(_param)

        prev_default_assumptions = set(defaults.assumptions)
        try:
            # These assumptions will be used for deriving any
            # side-effects:
            defaults.assumptions = set(assumptions)
            if not isinstance(orig_judgment, Judgment):
                raise TypeError("May only 'instantiate' a Judgment")
            if orig_judgment.proof() is None:
                raise UnusableProof(Judgment.theorem_being_proven,
                                    orig_judgment)

            # Perform relabeling of Judgment assumptions,
            # recording requirements.
            orig_subbed_assumptions = []
            requirements = []
            equality_repl_requirements = set()
            for assumption in orig_judgment.assumptions:
                assumption_was_expr_range = False
                if isinstance(assumption, ExprRange):
                    assumption = ExprTuple(assumption)
                    assumption_was_expr_range = True
                subbed_assumption = Lambda._apply(
                    relabel_params, assumption, *relabel_param_replacements,
                    param_to_num_operand_entries=param_to_num_operand_entries,
                    allow_relabeling=True, equiv_alt_expansions=None,
                    requirements=requirements)
                with defaults.temporary() as temp_defaults:
                    temp_defaults.auto_simplify = False
                    subbed_assumption = subbed_assumption.equality_replaced(
                            requirements=requirements)
                equality_repl_requirements.update(requirements)
                if assumption_was_expr_range:
                    # Expand a tuple of assumptions.
                    orig_subbed_assumptions.extend(
                            subbed_assumption.entries)
                else:
                    orig_subbed_assumptions.append(subbed_assumption)


            # Automatically use the assumptions of the
            # original_judgment plus the assumptions that were
            # provided.
            assumptions = tuple(orig_subbed_assumptions) + assumptions
            # Eliminate duplicates.
            assumptions = tuple(OrderedDict.fromkeys(assumptions))
            # Make these the new default assumptions (for side-effects).
            defaults.assumptions = assumptions
            
            # Perform the instantiations, recording requirements.
            instantiated_expr = \
                Instantiation._instantiated_expr(orig_judgment, 
                    relabel_params, relabel_param_replacements,
                    param_to_num_operand_entries,
                    num_forall_eliminations, repl_map,
                    equiv_alt_expansions, assumptions, requirements,
                    equality_repl_requirements)

            # Remove duplicates in the requirements.
            requirements = list(OrderedDict.fromkeys(requirements))

            # Remove any unnecessary assumptions (but keep the order
            # that was provided).  Note that some assumptions of
            # requirements may not be in the 'applied_assumptions_set'
            # if they made use of internal assumptions from a
            # Conditional and can be eliminated.
            applied_assumptions_set = set(assumptions)
            assumptions = list(orig_subbed_assumptions)
            for requirement in requirements:
                for assumption in requirement.assumptions:
                    if assumption in applied_assumptions_set:
                        assumptions.append(assumption)
            assumptions = list(OrderedDict.fromkeys(assumptions))

            # Map variables to sets of tuples that represent the
            # same range of indexing for equivalent alternative
            # expansions.  For example,
            #   {x_1, ..., x_{n+1}, x_1, ..., x_n, x_{n+1}}.
            var_range_forms = dict()
            for var_range_form, expansion in equiv_alt_expansions.items():
                var = get_param_var(var_range_form[0])
                var_range_forms.setdefault(var, set()).add(var_range_form)
            
            # Sort the replaced variables in order of their appearance
            # in the original Judgment.
            def get_key_var(key):
                if isinstance(key, ExprTuple):
                    assert key.num_entries() >= 1
                    var = get_param_var(key[0])
                    var_range_forms.setdefault(var, set()).add(key)
                    return var
                elif isinstance(key, IndexedVar):
                    var = get_param_var(key)
                    var_range_forms.setdefault(var, set()).add(key)
                    # For convenience to be used below:
                    equiv_alt_expansions[key] = repl_map[key]
                    return var
                return get_param_var(key)
            repl_var_keys = {get_key_var(key): key for key in repl_map.keys()}
            repl_vars = repl_var_keys.keys()
            repl_vars = list(orig_judgment.order_of_appearance(repl_vars))
            # And remove duplicates.
            repl_vars = list(OrderedDict.fromkeys(repl_vars))

            # We have what we need; set up the Instantiation Proof
            self.orig_judgment = orig_judgment
            # Exclude anything in the repl_map that does not appear in
            # the original Judgment:
            mapping = dict()
            mapping_key_order = []

            def var_range_form_sort(var_form):
                # For sorting equivalent ExprTuples of indexed
                # variables (e.g., {(x_1, ..., x_{n+1}),
                #                   (x_1, ..., x_n, x_{n+1})})
                # put ones with the fewest number of entries first
                # but break ties arbitrarily via the "meaning id".
                if isinstance(var_form, ExprTuple):
                    return (var_form.num_entries(), var_form._meaning_id)
                else:
                    return (0, var_form._meaning_id)
            for var in repl_vars:
                if var in repl_map:
                    # The variable itself is in the replacement map.
                    replacement = repl_map[var]
                    if isinstance(replacement, Lambda):
                        # If the replacement is a Lambda, convert it
                        # to a Function mapping form.
                        if var in replacement.parameters:
                            # We don't want any of the parameters of 
                            # the Lambda replacement to be the same as
                            # the function variable (e.g. i(i) = ...
                            # doesn't make sense in its appearance).
                            safe_var = safe_dummy_var(
                                var, replacement, replacement.parameters)
                            replacement = replacement.relabeled(
                                {var:safe_var})
                        key = Function(
                            var, replacement.parameter_or_parameters)
                        replacement = replacement.body
                    else:
                        key = var
                    mapping[key] = replacement
                    mapping_key_order.append(key)
                if var in var_range_forms:
                    # There are replacements for various forms of the
                    # variable indexed over the same range.
                    # We'll sort these in an order going
                    # from the fewest # of entries to the most.
                    for var_range_form in sorted(var_range_forms[var],
                                                 key=var_range_form_sort):
                        mapping[var_range_form] = \
                            equiv_alt_expansions[var_range_form]
                        mapping_key_order.append(var_range_form)
            self.mapping_key_order = mapping_key_order
            self.mapping = mapping
            instantiated_truth = Judgment(instantiated_expr, assumptions)
            # Make the 'original judgment' be the 1st requirement.
            requirements.insert(0, orig_judgment)
            # Mark the requirements that are "equality replacements".
            marked_req_indices = set()
            for k, req in enumerate(requirements):
                if req in equality_repl_requirements:
                    marked_req_indices.add(k)
            Proof.__init__(self, instantiated_truth, requirements,
                           marked_req_indices)
        except LambdaApplicationError as e:
            raise InstantiationFailure(orig_judgment, repl_map,
                                       assumptions, str(e))
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def _generate_step_info(self, object_rep_fn):
        '''
        Generate information about this proof step, including mapping
        information for this instantiation.
        '''
        mapping = self.mapping
        mapping_info = ','.join(
            object_rep_fn(key) +
            ':' +
            object_rep_fn(
                mapping[key]) for key in self.mapping_key_order)
        return self.step_type() + ':{' + mapping_info + '}'

    def step_type(self):
        return 'instantiation'

    def _single_mapping(self, key, replacement, format_type):
        def formatted(expr): return expr._repr_html_(
        ) if format_type == 'HTML' else str(expr)
        return formatted(key) + ' : ' + formatted(replacement)

    def _mapping(self, format_type='HTML'):
        if format_type == 'HTML':
            out = '<span style="font-size:20px;">'
        else:
            out = ''
        out += ', '.join(self._single_mapping(key,
                                              self.mapping[key],
                                              format_type) for key in self.mapping_key_order)
        if format_type == 'HTML':
            out += '</span>'
        return out

    @staticmethod
    def _get_nested_param_vars(expr, num_nested_foralls):
        '''
        Assuming the given 'expr' has at least 'num_nested_foralls'
        levels of directly nested universal quantifications,
        return the set of parameter varaibles for these quantifications.
        '''
        from proveit import Lambda, Conditional
        from proveit.logic import Forall
        param_vars = set()
        orig_expr = expr
        for _ in range(num_nested_foralls):
            if not isinstance(expr, Forall):
                raise ValueError(
                    "Improper 'num_forall_eliminations': "
                    "%s does not have %d nested Forall expressions."
                    % (orig_expr, num_nested_foralls))
            lambda_expr = expr.operand
            if not isinstance(lambda_expr, Lambda):
                raise TypeError(
                    "Forall Operation 'operand' must be a Lambda")
            param_vars.update(lambda_expr.parameter_var_set)
            expr = lambda_expr.body
            if isinstance(expr, Conditional):
                expr = expr.value
        return param_vars

    @staticmethod
    def _instantiated_expr(original_judgment, 
                           relabel_params, relabel_param_replacements,
                           param_to_num_operand_entries,
                           num_forall_eliminations,
                           repl_map, equiv_alt_expansions,
                           assumptions, requirements,
                           equality_repl_requirements):
        '''
        Return the instantiated version of the right side of the
        original_judgment.
        
        Eliminates the specified number of Forall operations,
        substituting all  of the corresponding instance variables
        according to repl_map.
        '''
        from proveit import (Variable, Lambda, Conditional, ExprTuple,
                             ExprRange, IndexedVar)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            get_param_var
        from proveit.logic import Forall, And
        # Eliminate the desired number of Forall operations and extract
        # appropriately mapped conditions.
        # Start with replacing the variables that are being relabeled
        # on both sides of the turnstile and then successively include
        # parameters as their universal quantifier is eliminated.
        expr = original_judgment.expr
        params = list(relabel_params)
        param_vars = {get_param_var(param) for param in params}
        operands = list(relabel_param_replacements)
        equiv_alt_expansion_keys_by_param_var = dict()
        for key in equiv_alt_expansions.keys():
            equiv_alt_expansion_keys_by_param_var.setdefault(
                get_param_var(key.entries[0]), []).append(key)
        active_equiv_alt_expansions = dict()

        def raise_failure(msg):
            raise InstantiationFailure(original_judgment, repl_map,
                                       assumptions, msg)
        
        def instantiate(expr):
            '''
            Instantiate the given expression by applying an
            ad-hoc Lambda mapping of the active params
            and operands.
            '''
            if len(params) == 0:
                return expr
            instantiated = Lambda._apply(
                params, expr, *operands, 
                param_to_num_operand_entries=param_to_num_operand_entries,
                allow_relabeling=True,
                equiv_alt_expansions=active_equiv_alt_expansions,
                requirements=requirements)
            new_equality_repl_requirements = []
            eq_replaced = instantiated.equality_replaced(
                    requirements=new_equality_repl_requirements,
                    auto_simplify_top_level=False)
            requirements.extend(new_equality_repl_requirements)
            equality_repl_requirements.update(new_equality_repl_requirements)
            return eq_replaced

        with defaults.temporary() as temp_defaults:
            # We don't want to simplify or make replacements when
            # instantiating indices of parameters or conditions.
            temp_defaults.preserve_all = True
            remaining_forall_eliminations = num_forall_eliminations
            while remaining_forall_eliminations > 0:
                remaining_forall_eliminations -= 1
                assert isinstance(expr, Forall)
                lambda_expr = expr.operand
                assert isinstance(lambda_expr, Lambda)
                expr = lambda_expr.body
                
                # Append to params and operands for new parameter
                # variables as the parameter quantifiers are 
                # eliminated.
                # Check for implicit variable range substitutions
                # that need to be made explicit.  For example,
                # if we have an instantiation for 'x' that is an 
                # ExprTuple and 'x' is universally quantified over a 
                # range here (e.g., x_1, ..., x_n), we will use the 
                # replacement of 'x' as the operands corresponding to
                # the x_1, ..., x_n parameters.  Also activate
                # equivalent alternative expansions (of such ranges)
                # as appropriate.
                for param in lambda_expr.parameters:
                    param_var = get_param_var(param)
                    if param_var in param_vars:
                        # The replacement for this parameter variable
                        # is already included.
                        continue
                    param_vars.add(param_var)
                    param_var_repl = repl_map.get(param_var, None)
                    new_param = None
                    new_operands = None
                    if (isinstance(param_var_repl, Variable)
                            and isinstance(param, ExprRange)):
                        # Instantiate a variable with a variable
                        # even though the param is an ExprRange.
                        new_param = param_var
                        new_operands = (param_var_repl,)
                    elif (isinstance(param, ExprRange) 
                             or isinstance(param, IndexedVar)):
                        subbed_param = instantiate(param)
                        subbed_param_tuple = ExprTuple(subbed_param)
                        new_param = subbed_param
                        if param_var_repl is not None:
                            # The replacement of the variable of an 
                            # ExprRange must be an ExprTuple.
                            if not isinstance(param_var_repl, ExprTuple):
                                raise_failure(
                                        "The replacement of a parameter "
                                        "variable for an ExprRange "
                                        "parameter must be an ExprTuple, "
                                        "got %s as replacement for "
                                        "variable of %s"
                                        %(param_var_repl, param))
                        if subbed_param_tuple in repl_map:
                            # There exists an explicit range
                            # instantiation.  For example,
                            # (x_1, ..., x_n): (a, b, c) or 
                            # (x_1): (z) if reduced to a singular 
                            # instance.
                            new_operands = repl_map[subbed_param_tuple]
                            assert isinstance(new_operands, ExprTuple)
                            if (param_var_repl is not None and
                                    param_var_repl != new_operands):
                                # An implicit and explicit range
                                # instantiation do not agree.
                                raise_failure("Inconsistent assignment of "
                                              "%s: %s, from instantiation "
                                              "of %s, versus %s."
                                              % (subbed_param_tuple,
                                                 param_var_repl, param_var,
                                                 new_operands))
                            new_operands = new_operands.entries
                        elif (not isinstance(subbed_param, ExprRange)
                              and subbed_param in repl_map):
                            # There exists an explicit instantiation of
                            # the singular instance.  For example,
                            # x_1: z
                            new_operands = (repl_map[subbed_param],)
                            if (param_var_repl is not None and
                                    param_var_repl.entries != new_operands):
                                # An implicit and explicit range
                                # instantiation do not agree.
                                raise_failure("Inconsistent assignment of "
                                              "%s: %s, from instantiation "
                                              "of %s, versus %s."
                                              % (subbed_param, param_var_repl, 
                                                 param_var, new_operands))
                        elif param_var_repl is not None:
                            # We have an implicit range instantiation.
                            # For example, x: (a, b, c).
                            new_operands = param_var_repl.entries   
                    elif param_var_repl is not None:
                        new_param = param
                        new_operands = (param_var_repl,)
                    # Update the active equivalent alternative expansions.
                    equiv_alt_expansion_keys = \
                        equiv_alt_expansion_keys_by_param_var.get(
                                param_var, None)
                    if equiv_alt_expansion_keys is not None:
                        active_equiv_alt_expansions.update(
                            {key:equiv_alt_expansions[key] for key 
                             in equiv_alt_expansion_keys})
                        if (new_operands is None 
                                and isinstance(param, ExprRange)):
                            # For the equivalent alternative expansion 
                            # to be used, we need to include the 
                            # parameter and corresponding operands; 
                            # in this case, it is a trivial identity 
                            # replacement.
                            if new_param is None:
                                new_param = param
                            new_operands = (new_param,)
                    if new_operands is not None:
                        params.append(new_param)
                        operands.extend(new_operands)
                        param_to_num_operand_entries[new_param]=(
                            len(new_operands))
                
                # If there is a condition of the universal quantifier
                # being eliminated, produce the instantiated condition,
                # prove that this is satisfied and add it as
                # "requirements".  When there is a conjunction of
                # multiple conditions, separate out a requirement for 
                # each individual condition (the operands of the
                # conjunction).
                if isinstance(expr, Conditional):
                    condition = expr.condition
                    expr = expr.value
    
                    # Instantiate the condition.
                    subbed_cond = instantiate(condition)
                    if isinstance(subbed_cond, And):
                        # It is important to deal with a conjunction
                        # condition in this implicit manner here or we
                        # would have a chicken/egg infinite recursion
                        # problem.  That is, we have to split up a
                        # conjunction into  multiple requirements at
                        # some point, so we do it there.
                        if subbed_cond.proven(assumptions):
                            # If the full condition conjunction is known
                            # to be true, we'll just use that as the
                            # requirement and be done with it.
                            requirements.append(subbed_cond.prove(
                                    assumptions=assumptions))
                            subbed_conds = []
                        else:
                            subbed_conds = subbed_cond.operands
                    else:
                        subbed_conds = [subbed_cond]
    
                    for subbed_cond in subbed_conds:
                        if isinstance(subbed_cond, ExprRange):
                            # If the substituted condition "entry" is
                            # a range, we need to wrap it in a
                            # conjunction.
                            subbed_cond = And(subbed_cond)
                        try:
                            requirements.append(subbed_cond.prove(
                                    assumptions=assumptions))
                        except ProofFailure:
                            raise_failure('Unsatisfied condition: %s'
                                          % str(subbed_cond))

        # Make final instantiations in the inner instance expression.
        # Add to the lambda-application parameters anything that has
        # not yet been used
        return instantiate(expr)


class Generalization(Proof):
    def __init__(
            self,
            instance_truth,
            new_forall_param_lists,
            new_conditions=tuple()):
        '''
        A Generalization step wraps a Judgment (instance_truth) in one or more Forall operations.
        The number of Forall operations introduced is the number of lists in new_forall_var_lists.
        The conditions are introduced in the order they are given at the outermost level that is
        applicable.  For example, if new_forall_param_lists is [[x, y], z]  and the new
        conditions are f(x, y) and g(y, z) and h(z), this will prove a statement of the form:
            forall_{x, y in Integer | f(x, y)} forall_{z | g(y, z), h(z)} ...
        '''
        from proveit import Judgment
        from proveit._core_.expression.expr import free_vars
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (get_param_var)
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        from proveit.logic import Forall
        if not isinstance(instance_truth, Judgment):
            raise GeneralizationFailure(
                None, [], 'May only generalize a Judgment instance')
        # the assumptions required for the generalization are the assumptions of
        # the original Judgment minus the all of the new conditions (including those
        # implied by the new domain).
        assumptions = set(instance_truth.assumptions)
        prev_default_assumptions = defaults.assumptions
        # these assumptions will be used for deriving any side-effects
        defaults.assumptions = assumptions
        try:
            if isinstance(new_conditions, ExprTuple):
                remaining_conditions = list(new_conditions.entries)
            else:
                remaining_conditions = list(new_conditions)
            expr = instance_truth.expr
            introduced_forall_vars = set()
            for k, new_forall_params in enumerate(
                    reversed(new_forall_param_lists)):
                new_forall_vars = [get_param_var(parameter)
                                   for parameter in new_forall_params]
                introduced_forall_vars |= set(new_forall_vars)
                new_conditions = []
                if k == len(new_forall_param_lists) - 1:
                    # the final introduced Forall operation must use all of the
                    # remaining conditions
                    new_conditions = remaining_conditions
                else:
                    # use all applicable conditions in the supplied order
                    condition_applicability = \
                        [not free_vars(remaining_cond).isdisjoint(
                            new_forall_vars)
                         for remaining_cond in remaining_conditions]
                    new_conditions = \
                        [remaining_cond for applicable, remaining_cond
                         in zip(condition_applicability, remaining_conditions)
                         if applicable]
                    remaining_conditions = \
                        [remaining_cond for applicable, remaining_cond
                         in zip(condition_applicability, remaining_conditions)
                         if not applicable]
                # new conditions can eliminate corresponding assumptions
                assumptions -= set(new_conditions)
                # create the new generalized expression
                generalized_expr = Forall(
                    instance_param_or_params=new_forall_params,
                    instance_expr=expr, conditions=new_conditions)
                # make sure this is a proper generalization that doesn't break
                # the logic:
                Generalization._checkGeneralization(generalized_expr, expr)
                expr = generalized_expr
            for assumption in assumptions:
                if not free_vars(assumption).isdisjoint(
                        introduced_forall_vars):
                    raise GeneralizationFailure(
                        generalized_expr,
                        assumptions,
                        'Cannot generalize using assumptions that involve any of the new forall variables (except as assumptions are eliminated via conditions or domains)')
            generalized_truth = Judgment(generalized_expr, assumptions)
            self.instance_truth = instance_truth
            self.new_forall_vars = new_forall_vars
            self.new_conditions = new_conditions
            Proof.__init__(self, generalized_truth, [self.instance_truth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def step_type(self):
        return 'generalization'

    @staticmethod
    def _checkGeneralization(generalized_expr, instance_expr):
        '''
        Make sure the generalized_expr is a proper generalization of the
        instance_expr.
        '''
        from proveit import Lambda, Conditional
        from proveit.logic import Forall
        assert isinstance(
            generalized_expr, Forall), 'The result of a generalization must be a Forall operation'
        lambda_expr = generalized_expr.operand
        assert isinstance(
            lambda_expr, Lambda), 'A Forall Expression must be in the proper form'
        expr = lambda_expr.body
        while expr != instance_expr:
            if isinstance(expr, Conditional):
                # Dig into the conditional.  Adding conditions only
                # weakens the statement, so it doesn't matter what
                # the conditions are.
                expr = expr.value
                if expr == instance_expr:
                    break
            if not isinstance(expr, Forall):
                break
            expr = expr.instance_expr  # take it another nested level if necessary
        assert expr == instance_expr, 'Generalization not consistent with the original expression: ' + \
            str(expr) + ' vs ' + str(instance_expr)


class _ShowProof:
    '''
    A mocked-up quasi-Proof object just for the purposes of showing a
    stored proof.
    '''

    # Map proof_id's to _ShowProof objects that have been created.
    show_proof_by_id = dict()

    def __init__(self, theory, folder, proof_id, step_info,
                 ref_obj_id_groups):
        self._style_id = proof_id
        if '_' in step_info:
            # Must be an axiom or theorem with the format
            # axiom_theory.name or theorem_theory.name
            self.step_type_str, full_name = step_info.split('_', 1)
            assert self.step_type_str in ('axiom', 'theorem')
            full_name_segments = full_name.split('.')
            theory_name = '.'.join(full_name_segments[:-1])
            self.theory = Theory.get_theory(theory_name)
            self.name = full_name_segments[-1]
        else:
            self.theory = theory
            self.step_type_str = step_info
        self.theory_folder_storage = theory_folder_storage = \
            self.theory._theory_folder_storage(folder)
        if self.step_type_str == 'instantiation':
            # Extract the mapping information.
            group = ref_obj_id_groups[0]
            key_mapping_pairs = \
                [(theory_folder_storage.make_expression(group[i]),
                  theory_folder_storage.make_expression(group[i + 1]))
                    for i in range(0, len(group), 2)]
            self.mapping_key_order = [key for key, value in key_mapping_pairs]
            self.mapping = dict(key_mapping_pairs)
        self.proven_truth = \
            theory_folder_storage.make_judgment_or_proof(
                ref_obj_id_groups[-2][0])
        self.proven_truth._meaning_data._proof = self
        self.required_proofs = \
            [theory.get_show_proof(obj_id.rstrip('*'), folder) for obj_id
             in ref_obj_id_groups[-1]]
        self.marked_required_truth_indices = \
            {k for k, obj_id in enumerate(ref_obj_id_groups[-1])
             if obj_id[-1] == '*'}
        _ShowProof.show_proof_by_id[proof_id] = self

    def _repr_html_(self):
        if not defaults.display_latex:
            return None  # No LaTeX display at this time.
        return Proof._repr_html_(self)

    def step_type(self):
        return self.step_type_str

    def get_link(self):
        from ._theory_storage import StoredAxiom, StoredTheorem
        if self.step_type_str == 'axiom':
            return StoredAxiom(self.theory, self.name).get_def_link()
        elif self.step_type_str in ('theorem', 'conjecture'):
            return StoredTheorem(self.theory, self.name).get_proof_link()
        else:
            return self.theory_folder_storage.proof_notebook(self)

    def _single_mapping(self, *args):
        return Instantiation._single_mapping(self, *args)

    def _mapping(self, *args):
        return Instantiation._mapping(self, *args)

    def enumerated_proof_steps(self):
        return Proof.enumerated_proof_steps(self)

    def is_usable(self):
        return True


class ProofFailure(Exception):
    def __init__(self, expr, assumptions, message):
        self.expr = expr
        self.message = message
        self.assumptions = assumptions
        self.automation = defaults.automation

    def __str__(self):
        if self.automation:
            automation_str = ""
        else:
            automation_str = " without automation"
        if len(self.assumptions) == 0:
            assumptions_str = ""
        else:
            assumptions_str = " assuming {" + ", ".join(
                str(assumption) for assumption in self.assumptions) + "}"
        if self.expr is not None:
            return ("Unable to prove " + str(self.expr) + automation_str 
                    + assumptions_str + ":\n" + self.message)
        else:
            return ("Proof step failed" + automation_str 
                    + assumptions_str + ":\n" + self.message)

class UnsatisfiedPrerequisites(Exception):
    def __init__(self, msg):
        self.msg = msg
    
    def __str__(self):
        return "Prerequisites not met: " + self.msg

class ModusPonensFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)


class InstantiationFailure(ProofFailure):
    def __init__(self, original_judgment, repl_map, assumptions, message):
        message = "Attempting to instantiate %s with %s:\n%s" % (
            original_judgment, repl_map, message)
        ProofFailure.__init__(self, None, assumptions, message)


class GeneralizationFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)


class UnusableProof(ProofFailure):
    def __init__(self, proving_theorem, unusable_proof, extra_msg=''):
        ProofFailure.__init__(
            self,
            unusable_proof.proven_truth.expr,
            [],
            "Unusable Proof")
        self.proving_theorem = proving_theorem
        self.unusable_proof = unusable_proof
        self.extra_msg = '; ' + extra_msg

    def __str__(self):
        if self.proving_theorem == self.unusable_proof:
            return "Cannot use %s to prove itself" % str(self.proving_theorem)
        if isinstance(
                self.unusable_proof,
                Theorem) or isinstance(
                self.unusable_proof,
                Axiom):
            unusuable_proof_str = str(self.unusable_proof)
        else:
            unusuable_proof_str = str(self.unusable_proof.proven_truth)
        if self.proving_theorem is not None:
            return unusuable_proof_str + ' is not usable while proving ' + \
                str(self.proving_theorem) + ' (it has not been presumed)' + self.extra_msg
        else:
            return 'Cannot use disabled proof for ' + self.unusable_item_str


class CircularLogic(Exception):
    def __init__(self, proving_theorem, presumed_theorem, implicitly_presumed=False):
        self.proving_theorem = proving_theorem
        self.presumed_theorem = presumed_theorem
        self.implicitly_presumed = implicitly_presumed

    def __str__(self):
        if self.implicitly_presumed:
            return str(self.presumed_theorem) + ' cannot be implicitly presumed while proving ' + \
                str(self.proving_theorem) + ' due to a circular dependence/presumptions; it must be excluded.'
        else:
            return str(self.presumed_theorem) + ' cannot be explicitly presumed while proving ' + \
                str(self.proving_theorem) + ' due to a circular dependence/presumptions.'


"""
class CircularLogicLoop(ProofFailure):
    def __init__(self, presumption_loop, presumed_theorem):
        assert presumption_loop[0] == presumption_loop[-1], "expecting a loop"
        assert str(
            presumed_theorem) == presumption_loop[0], "expecting presumed_theorem to match the ends of the presumption_loop"
        CircularLogic.__init__(
            self,
            Judgment.theorem_being_proven,
            presumed_theorem)
        self.presumption_loop = presumption_loop

    def __str__(self):
        return "Circular presumption dependency detected: %s" % str(
            self.presumption_loop)
"""
