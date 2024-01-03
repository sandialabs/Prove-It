"""
A Proof is a directed, acyclic graph (DAG) that represents the Prove-It
proof for a Judgment.  Each object represents a derivation step
(Assumption, ModusPonens, Deduction, Specialization,
or Generalization) and has references to other Judgments that
are directly required, each with its Proof.  In this way, the
Proof objects form a DAG.
"""

from collections import OrderedDict, deque
import re
import sys
from proveit._core_.judgment import Judgment
from proveit._core_._unique_data import meaning_data, style_data
from .defaults import defaults, USE_DEFAULTS
from .theory import Theory


class Proof:

    # (Expression, sorted assumptions) pairs for which 
    # derive_side_effects has been called.  We track this to make sure 
    # we didn't miss anything while automation was disabled and then 
    # re-enabled.
    sideeffect_processed = set()    
    
    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information in
        the Proof jurisdiction.
        '''
        Proof.sideeffect_processed.clear()
        Assumption.all_assumptions.clear()
        Assumption.considered_assumption_sets.clear()
        Theorem.all_theorems.clear()
        Instantiation.instantiations.clear()
        Instantiation.unsatisfied_condition = None
        Instantiation.condition_assumptions = None
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
            self._meaning_data._non_allowances = None
            # being applied directly or indirectly.

        # The style data is shared among Proofs with the same structure and
        # style.
        self._style_data = style_data(
            self._generate_unique_rep(
                lambda obj: hex(
                    obj._style_id)))

        # Reference this unchanging data of the unique 'meaning' data.
        self._meaning_id = self._meaning_data._unique_id
        self._style_id = self._style_data._unique_id

        # Reference this data of the unique 'meaning' data, but note 
        # that these are subject to change (as proofs are disabled and 
        # as new dependencies are added).
        self.required_proofs = self._meaning_data.required_proofs
        self._dependents = self._meaning_data._dependents

        # If there is literal generalization, we need to
        # indicate appropriate eliminations.
        if (proven_truth.num_lit_gen > 0 and 
                not hasattr(self, '_eliminated_axioms')):
            from ._theory_storage import StoredTheorem
            # First collect all of the eliminations from the 
            # required proofs.
            eliminated_proof_steps = set()
            eliminated_axioms = set()
            eliminated_defining_properties = set()
            eliminated_theorems = set()
            for required_proof in self.required_proofs:
                eliminated_proof_steps.update(
                    required_proof.eliminated_proof_steps())
                eliminated_axioms.update(
                    required_proof.eliminated_axioms())
                eliminated_defining_properties.update(
                    required_proof.eliminated_defining_properties())
                eliminated_theorems.update(
                    required_proof.eliminated_theorems())
            # Now see if any of these are reintroduced through
            # side-channels.
            proofs_to_check__to__nonelims = dict()
            for eliminated_set in (eliminated_proof_steps,
                                   eliminated_axioms,
                                   eliminated_defining_properties,
                                   eliminated_theorems):
                # Collect subsets of the required proofs that aren't 
                # eliminating a particular Proof, and map such subsets 
                # to the set of mutually non-eliminated Proofs.
                for _elim in eliminated_set:
                    proofs_to_check = set()
                    for _proof in self.required_proofs:
                        if not _proof.is_eliminated(_elim):
                            proofs_to_check.add(_proof)
                    proofs_to_check__to__nonelims.setdefault(
                        frozenset(proofs_to_check), set()).add(_elim)
            # For each subset of required proofs that doesn't
            # eliminate something, search it to see if any of these
            # non-eliminated items are reintroduced.
            for proofs_to_check, nonelims in (
                    proofs_to_check__to__nonelims.items()):
                # Get all local Proof requirements.
                if len(eliminated_proof_steps) > 0 and (
                        not all(isinstance(nonelim, Axiom) 
                                or isinstance(nonelim, Theorem) 
                                for nonelim in nonelims)):
                    # We need to make sure proofs steps are eliminated
                    # for each requirement separately.
                    _proofs = set().union(*[proof.all_required_proofs() for
                                            proof in proofs_to_check])
                    # Might backtrack on eliminating proofs steps.
                    eliminated_proof_steps -= _proofs.intersection(nonelims)
                else:
                    # No proof steps to eliminate.
                    _proofs = Proof.requirements_of_proofs(proofs_to_check)
                # Get all direct/indirect Axiom/Theorem requirements.
                axioms_to_check, def_props_to_check, thms_to_check, _ = (
                    StoredTheorem.requirements_of_theorems(
                        [_proof for _proof in _proofs 
                         if isinstance(_proof, Theorem)]))
                # Might backtrack on eliminated axioms/theorems.
                axiom_violations = axioms_to_check.intersection(nonelims)
                eliminated_axioms -= axiom_violations
                defining_property_violations = def_props_to_check.intersection(
                    nonelims)
                eliminated_defining_properties -= defining_property_violations
                thm_violations = thms_to_check.intersection(nonelims)
                eliminated_theorems -= thm_violations
            # These should be good to go now:
            self._eliminated_proof_steps = frozenset(
                eliminated_proof_steps)
            self._eliminated_axioms = frozenset(eliminated_axioms)
            self._eliminated_defining_properties = frozenset(
                eliminated_defining_properties)
            self._eliminated_theorems = frozenset(eliminated_theorems)

        all_required_proofs = self.all_required_proofs()
        if not hasattr(self._meaning_data, 'num_steps'):
            # determine the number of unique steps required for this proof
            self._meaning_data.num_steps = len(all_required_proofs)
        
        # See if this is a useless self-dependent proof
        all_required_truths = {required_proof.proven_truth for
                               required_proof in all_required_proofs
                               if required_proof is not self}
        useless_proof = proven_truth in all_required_truths
        if useless_proof:
            # not usable because it is not useful
            self._meaning_data._unusable_proof = self  
            assert proven_truth.proof() is not None, (
                "There should have been an 'original' proof")
            return
        else:
            # As long as this is not a useless self-dependent proof (a 
            # proof that depends upon a different proof of the same
            # truth which should never actually get used), track the 
            # dependencies of required proofs so they can be updated 
            # appropriately if there are changes due to proof disabling.
            for required_proof in self.required_proofs:
                required_proof._dependents.add(self)

        requiring_unusable_proof = False
        for required_proof in self.required_proofs:
            if required_proof.is_possibly_usable():
                # Record any required theorems that are not explicitly
                # allowed.  We'll wait until displaying a Judgement 
                # whose Proof isn't explicitly allowed to query the
                # user about whether to allow or disallow
                # these.
                if not required_proof.explicitly_allowed():
                    if self._meaning_data._non_allowances is None:
                        self._meaning_data._non_allowances = set()
                    self._meaning_data._non_allowances.update(
                            required_proof._meaning_data._non_allowances)
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
        if self.is_possibly_usable():
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

        # Record that this is proven whether side-effect automation is
        # enabled or not.
        self.proven_truth.expr._record_as_proven(self.proven_truth)         
        
        # Derive obvious consequences from this truth.
        self._derive_side_effects()

    def regenerate_proof_object(self, simplify_only_where_marked=False,
                                markers_and_marked_expr=None):
        '''
        Regenerate this proof object under active defaults which may
        effect simplifications or replacements.
        '''
        if len(defaults.replacements) == 0 and not defaults.auto_simplify:
            # The active defaults will not induce any changes.
            return self
        all_requirements = list(self.required_truths)
        eq_replaced_expr = self.proven_truth.expr.equality_replaced(
            requirements=all_requirements,
            auto_simplify_top_level=False,
            simplify_only_where_marked=simplify_only_where_marked,
            markers_and_marked_expr=markers_and_marked_expr)
        if eq_replaced_expr == self.proven_truth.expr:
            return self # No change.

        # Remove any unnecessary assumptions (but keep the order
        # that was provided).  Note that some assumptions of
        # requirements may not be in the 'applied_assumptions'
        # if they made use of internal assumptions from a
        # Conditional and can be eliminated.
        applied_assumptions = defaults.assumptions
        assumptions = list(self.proven_truth.assumptions)
        for requirement in all_requirements[len(self.required_truths):]:
            for assumption in requirement.assumptions:
                if assumption in applied_assumptions:
                    assumptions.append(assumption)
        assumptions = list(OrderedDict.fromkeys(assumptions))
        proven_truth = Judgment(eq_replaced_expr, assumptions)
        # Mark the requirements that are "equality replacements".
        marked_req_indices = set(self.marked_required_truth_indices)
        for k in range(len(self.required_truths), len(all_requirements)):
            marked_req_indices.add(k)
        return self._regenerate_proof_object(
            proven_truth, all_requirements, marked_req_indices)

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        raise NotImplementedError("Must be implemented for each Proof "
                                  "object")
    
    def _derive_side_effects(self):
        '''
        Derive side-effects under the active assumptions if
        this proof is relevent.
        '''
        if not defaults.sideeffect_automation:
            return # Side-effect automation is off, so don't do it.
        proven_truth = self.proven_truth
        
        if proven_truth.proof() == self and self.is_possibly_usable(): 
            key = (proven_truth.expr, defaults.sorted_assumptions,
                   defaults.conclude_automation)
            if key in Proof.sideeffect_processed:
                return  # has already been processed

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
                #print(proven_truth)
                proven_truth.derive_side_effects()
            Proof.sideeffect_processed.add(key)

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
            if dependent._meaning_data._non_allowances is not None or (
                    newproof._meaning_data._non_allowances is not None):
                # The "non-allowances" must be updated.
                dependent._update_non_allowances()
            if all(required_proof.is_possibly_usable()
                   for required_proof in dependent.required_proofs):
                dependent._meaning_data._unusable_proof = None  # it is usable again
                dependent.proven_truth._add_proof(
                    dependent)  # add it back as an option
        # Nothing should depend upon the old proof any longer.
        oldproof._dependents.clear()      
    
    def _update_non_allowances(self):
        '''
        Update the set of directly or indirectly required proofs that
        are neither allowed nor disallowed.
        '''
        revised_non_allowance = set()
        for required_proof in self.required_proofs:
            if required_proof._meaning_data._non_allowances is not None:
                revised_non_allowance.update(
                        required_proof._meaning_data._non_allowances)
        if len(revised_non_allowance) == 0:
            self._meaning_data._non_allowances = None
        else:
            self._meaning_data._non_allowances = (
                    revised_non_allowance)

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
        kind, full_name = step_info.split('-', 1)
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

    def is_possibly_usable(self):
        '''
        Returns True iff this Proof is possibly usable (not manually 
        disabled or explicitly disallowed as a presumption while trying
        to prove a Theorem).
        '''
        return self._meaning_data._unusable_proof is None
    
    def explicitly_allowed(self):
        '''
        Returns True iff this Proof is explicitly allowed.
        '''
        return (self._meaning_data._unusable_proof is None and
                self._meaning_data._non_allowances is None)
    
    def _query_allowance(self):
        '''
        If the proof is neither explicitly allowed nor disallowed,
        force the user to make a choice.
        '''
        if self._meaning_data._unusable_proof is not None:
            return False # explicitly disallowed
        if self._meaning_data._non_allowances is None:
            return True # explicitly allowed
        name_to_thm = {str(proof):proof for proof in
                       self._meaning_data._non_allowances}
        for thm_name in sorted(name_to_thm.keys()):
            # We must make a choice for each of these (or cancel and
            # return False).
            thm = name_to_thm[thm_name]
            if not thm._query_allowance():
                return False
        # These are now all allowed.
        self._meaning_data._non_allowances = None
        return True

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
                                if proof.is_possibly_usable()]

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
            # Make the number of steps (and number of literal 
            # generalizations) as unknown as we go up through
            # the dependents.
            dependent._meaning_data.num_steps = None
            dependent._meaning_data._num_lit_gen = None
            if not is_defunct:
                # A different proof was active, so we don't have
                # worry about its dependents.
                continue
            # Push sub-dependents onto the heap.
            for _dependent in dependent._dependents:
                if _dependent.is_possibly_usable():
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
            if dependent.is_possibly_usable():
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

    def _goodness(self):
        '''
        We determine the 'best' proof according to:
        1) the most literal generalization steps (which may eliminate
           axioms and/or theorems)
        2) the fewest number of proofs steps,
        3) the fewest number of assumptions,
        in that order.
        '''
        return (self.proven_truth.num_lit_gen, -self.num_steps(),
                -len(self.proven_truth.assumptions))

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
        Returns the set of Axioms that are used directly
        (not via other theorems) in this proof.
        '''
        axioms = set().union(
            *[required_proof.used_axioms()
              for required_proof in self.required_proofs])
        if self.proven_truth.num_lit_gen > 0:
            return axioms - self._eliminated_axioms
        return axioms
    
    def used_defining_properties(self):
        '''
        Returns the set of DefiningProperties that are used 
        directly (not via other theorems) in this proof.
        '''
        defining_properties = set().union(
            *[required_proof.used_defining_properties()
              for required_proof in self.required_proofs])
        if self.proven_truth.num_lit_gen > 0:
            return defining_properties - self._eliminated_defining_properties
        return defining_properties

    def used_theorems(self):
        '''
        Returns the set of Theorems that are used directly 
        (not via other theorems) in this proof.
        '''
        thms = set().union(
            *[required_proof.used_theorems()
              for required_proof in self.required_proofs])
        if self.proven_truth.num_lit_gen > 0:
            return thms - self._eliminated_theorems
        return thms

    def eliminated_proof_steps(self):
        '''
        Returns the set of proof steps (non Axiom or Theorem) that 
        are eliminated in this proof via literal generalization.
        '''
        if self.proven_truth.num_lit_gen > 0:
            return self._eliminated_proof_steps
        return frozenset()

    def eliminated_axioms(self):
        '''
        Returns the set of Axioms that are eliminated in this 
        proof via literal generalization.
        '''
        if self.proven_truth.num_lit_gen > 0:
            return self._eliminated_axioms
        return frozenset()

    def eliminated_defining_properties(self):
        '''
        Returns the set of DefiningProperties that are eliminated 
        in this proof via literal generalization.
        '''
        if self.proven_truth.num_lit_gen > 0:
            return self._eliminated_defining_properties
        return frozenset()

    def eliminated_theorems(self):
        '''
        Returns the set of Theorems that are eliminated in 
        this proof via literal generalization.
        '''
        if self.proven_truth.num_lit_gen > 0:
            return self._eliminated_theorems
        return frozenset()

    def is_eliminated(self, proof):
        '''
        Return True if the given Proof object is eliminated
        via literal generalization.
        '''
        if self.proven_truth.num_lit_gen > 0:
            if isinstance(proof, Axiom):
                return proof in self._eliminated_axioms
            if isinstance(proof, DefiningProperty):
                return proof in self._eliminated_defining_properties
            if isinstance(proof, Theorem):
                return proof in self._eliminated_theorems
            return proof in self._eliminated_proof_steps
        return False

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
            # It is okay to change the proven_truth to another one
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

    def all_required_proofs(self):
        '''
        Returns the set of directly or indirectly required Proofs,
        stopping at Assumptions, Axioms, or Theorems.
        '''
        return Proof.requirements_of_proofs(
            [self], exclusions=self.eliminated_proof_steps())

    @staticmethod
    def requirements_of_proofs(proofs, *, exclusions=None):
        '''
        Returns the set of Proof objects that are required (directly
        or indirectly) by the given Proofs, stopping at Assumptions,
        Axioms, or Theorems.
        '''
        requirements = set()
        to_process = set(proofs)
        while len(to_process) > 0:
            proof = to_process.pop()
            if exclusions is not None and proof in exclusions:
                continue # excluded
            if proof in requirements:
                continue # already processed this one
            requirements.add(proof)
            to_process.update(proof.required_proofs)
        return requirements

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
            if hasattr(self, '_steps_to_include'):
                if k not in self._steps_to_include:
                    continue
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
            if proof.step_type() == 'instantiation' and not hasattr(self, '_steps_to_include'):
                html += '<tr><td>&nbsp;</td><td colspan=4 style="text-align:left">' + \
                    proof._mapping('HTML') + '</td></tr>'
            elif proof.step_type() in {'axiom', 'theorem', 'conjecture',
                                       'defining_property'}:
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
            out_str += proof.proven_truth.string()
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
    considered_assumption_sets = set()    

    def __init__(self, expr, assumptions=None, *,
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
        from proveit import ExprRange
        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return
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

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        return Assumption(
            None, _proven_truth=proven_truth, _requirements=requirements,
            _marked_req_indices=marked_req_indices)

    @staticmethod
    def make_assumption(expr):
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
            preexisting._derive_side_effects()
            return preexisting
        return Assumption(expr, defaults.assumptions)

    @staticmethod
    def make_assumptions(assumptions=USE_DEFAULTS):
        '''
        Prove each assumption, by assumption, to deduce any 
        side-effects (unless we have already processed this set of
        assumptions together before).
        '''
        with defaults.temporary() as temp_defaults:
            if assumptions is not USE_DEFAULTS:
                temp_defaults.assumptions = assumptions
            assumptions = defaults.assumptions
            sorted_assumptions = defaults.sorted_assumptions            

            # avoid infinite recursion and extra work
            if sorted_assumptions not in Assumption.considered_assumption_sets:
                Assumption.considered_assumption_sets.add(sorted_assumptions)
                for assumption in assumptions:
                    # Note that while we only need THE assumption to 
                    # prove itself, having the other assumptions around 
                    # can be useful for deriving side-effects.
                    Assumption.make_assumption(assumption)
                if not defaults.sideeffect_automation:
                    # consideration doesn't fully count if automation is 
                    # off
                    Assumption.considered_assumption_sets.remove(
                            sorted_assumptions)

    def step_type(self):
        return 'assumption'


class Axiom(Proof):
    def __init__(self, expr, theory, name, *, 
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
        if not isinstance(theory, Theory):
            raise TypeError("An axiom 'theory' must be a Theory object")
        if not isinstance(name, str):
            raise TypeError("An axiom 'name' must be a string")
        self.theory = theory
        self.name = name
        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return
        else:
            Proof.__init__(self, Judgment(expr, frozenset()), [])

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        return Axiom(None, self.theory, self.name,
                     _proven_truth=proven_truth, _requirements=requirements,
                     _marked_req_indices=marked_req_indices)

    def _generate_step_info(self, object_rep_fn):
        return self.step_type() + '-' + str(self) + ':'

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

    def __init__(self, expr, theory, name, *,
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
        if not isinstance(theory, Theory):
            raise TypeError("A theorem 'package' must be a Theory object")
        if not isinstance(name, str):
            raise TypeError("A theorem 'name' must be a string")
        self.theory = theory
        self.name = name
        # keep track of proofs that may be used to prove the theorem
        # before 'begin_proof' is called so we will have the proof handy.
        self._possibleProofs = []
        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return
        else:
            # Note that _mark_usability will be called within Proof.__init__
            Proof.__init__(self, Judgment(expr, frozenset()), [])
        Theorem.all_theorems.append(self)

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        return Theorem(None, self.theory, self.name,
                       _proven_truth=proven_truth, _requirements=requirements,
                       _marked_req_indices=marked_req_indices)

    def _generate_step_info(self, object_rep_fn):
        # For these purposes, we should use 'theorem' even if the
        # status is 'conjecture'.
        return 'theorem-' + str(self) + ':'

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

    def get_allowed_and_disallowed_presumptions(self):
        '''
        Return the set of theorems and theory packages that are 
        allowed/disallowed to be presumed in the proof of this theorem.
        '''
        return self._stored_theorem().get_allowed_and_disallowed_presumptions()

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

    def all_requirements(self, *, sort_key=None):
        '''
        Returns the axioms that are required (directly or indirectly) 
        by the theorem.  Also, return the set of "dead-end" theorems 
        that are required (directly or indirectly).  A "dead-end" 
        theorem is either unproven or has an expression that matches 
        one in the optionally provided `dead_end_theorem_exprs`.
        Conservative definitions that are not logically necessary
        for the proof are extracted from these sets and returned on
        their own.

        Returns the list of axioms, "dead-end" theorems, and
        conservative definitions as a tuple.  These will be sorted
        according to sort_key with the exception that a conservatively
        defined literal will not appear before its definition in the
        list of conservative definitions.
        '''
        return self._stored_theorem().all_requirements(sort_key=sort_key)

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
        If this theorem is disallowed while proven the "theorem
        being proven" then it will be marked as unusable and set to
        disable.  If this theorem is allowed, we will ensure there is
        not a circular dependence among explicitly allowed or used
        theorems that brings us back to the "theorem being proven";
        this strikes a balance between being proactive about checking 
        for circularity and not burdening the system too much with 
        checking all theorems of an allowed package.  If this theorem
        is neither explicitly allowed nor disallowed, we will mark
        it as such in its _meaning_data._non_allowances which will
        be propagated through dependencies.  We will query the user
        whether to allow or disallow each theorem in such a limbo
        when displaying any Judgment whose Proof depends upon these 
        theorems.
        
        If set_to_disable is provided, instead of actively disabling
        proofs, collect them in a set to be disabled more efficiently.
        '''
        #from proveit.certify import is_fully_proven
        if Judgment.theorem_being_proven is None:
            # Nothing being proven, so all Theorems are usable
            self._meaning_data._unusable_proof = None
            return
        theorem_being_proven_str = Judgment.theorem_being_proven_str
        if self.proven_truth == Judgment.theorem_being_proven.proven_truth:
            # Note that two differently-named theorems for the same 
            # thing may exists in order to show an alternate proof.  
            # In that case, we want to disable the other alternates as 
            # well so we will be sure to generate the new proof.
            if set_to_disable is None:
                self.disable()
            else:
                set_to_disable.add(self)
            return
        
        name_and_containing_theories = list(
            self.theorem_name_and_containing_theories())
        
        # First let's check if this theorem or a containing theory
        # is explicitly disallowed.
        if not Judgment.disallowed_theorems_and_theories.isdisjoint(
                        name_and_containing_theories):
            # This Theorem is explicitly disallowed and therefore not 
            # usable while proving the "theorem being proven".  
            # Propagate this fact to all dependents.
            if set_to_disable is None:
                self.disable()
            else:
                set_to_disable.add(self)
            return
            
        # Next check to see if this theorem or a containing theory
        # is explicitly allowed.
        stored_theorem = self._stored_theorem()
        allowed_theorems_and_theories = (
                Judgment.allowed_theorems_and_theories)
        presumed_theorems_and_dependencies = (
                Judgment.presumed_theorems_and_dependencies)
        if not allowed_theorems_and_theories.isdisjoint(
                        name_and_containing_theories):
            # This theorem is explicitly allowed.  Let's recurse 
            # through explicitly allowed presumptions and used theorems
            # to see if anything leads back to the theorem being proven
            # and prevent the potential for circular logic.
            stored_theorem.all_used_or_presumed_theorem_names(
                presumed_theorems_and_dependencies)
            if theorem_being_proven_str in presumed_theorems_and_dependencies:
                # Theorem-specific presumption or dependency is
                # mutual.  Raise a CircularLogic error.
                specifically_presumed = (str(self) in 
                                     allowed_theorems_and_theories)
                raise CircularLogic(
                    Judgment.theorem_being_proven, self,
                    implicitly_presumed = not specifically_presumed)
        else:
            # It is neither allowed nor disallowed.  Record this
            # in the 'non_allowances'.
            self._meaning_data._non_allowances = {self}
            # Propagate to dependents.
            to_process = set(self._meaning_data._dependents)
            processed = {self}
            while len(to_process) > 1:
                dep_proof = to_process.pop()
                if dep_proof in processed: continue
                if dep_proof._meaning_data._non_allowances is None:
                    dep_proof._meaning_data._non_allowances = {self}
                else:
                    dep_proof._meaning_data._non_allowances.add(self)
                processed.add(dep_proof)
                to_process.update(dep_proof._meaning_data._dependents)

    def _query_allowance(self):
        '''
        If the Theorem is neither explicitly allowed nor disallowed,
        force the user to make a choice.
        '''
        name_and_containing_theories = list(
            self.theorem_name_and_containing_theories())
        if self._meaning_data._unusable_proof is not None or (
                not Judgment.disallowed_theorems_and_theories.isdisjoint(
                    name_and_containing_theories)):
            return False # explicitly disallowed
        if self._meaning_data._non_allowances is None or (
                not Judgment.allowed_theorems_and_theories.isdisjoint(
                        name_and_containing_theories)):
            return True # explicitly allowed
        assert (len(self._meaning_data._non_allowances)==1 and
                self in self._meaning_data._non_allowances)
        
        hint = ''
        used_theorem_names = self.all_used_or_presumed_theorem_names()
        if Judgment.theorem_being_proven_str in used_theorem_names:   
            hint = ("\nHint: %s based upon current proofs, this must be"
                    "\nDISALLOWED to prevent circular logic."%str(self))
        elif self.is_fully_proven():
            hint = ("\nHint: %s is fully proven and based upon current "
                    "proofs, \nit is safe to ALLOW."%str(self))
        
        # If running build.py, just raise an exception since there
        # is no user interactivity.
        if defaults._executing_auto_build:
            raise Exception(
                    "Attempting to use %s which has neither been allowed "
                    "nor disallowed for use in the proof of %s."
                    %(str(self), Judgment.theorem_being_proven_str))
        
        cur_level = str(self)
        print("Attempting to use %s which has neither been\n allowed nor "
              "disallowed for use in this proof.%s"%(str(self), hint))
        sys.stdout.flush()
        while True:
            # Query whether to allow, disallow, go up a level, 
            # or cancel.
            r = input("Do you wish to (a)llow, (d)isallow, go (u)p a level, "
                  "or (c)ancel? ")
            if r[0].lower() == 'a':
                # Add to allowances and return True.
                Judgment.stored_theorem_being_proven.allow_presumption(
                        cur_level)
                Judgment.allowed_theorems_and_theories.add(cur_level)
                self._meaning_data._non_allowances = None
                self._mark_usability()
                return True
            elif r[0].lower() == 'd':
                # Add to disallowances and return False.
                Judgment.stored_theorem_being_proven.disallow_presumption(
                        cur_level)
                Judgment.disallowed_theorems_and_theories.add(cur_level)
                self._mark_usability()
                return False
            elif r[0].lower() == 'u':
                # go up a level
                cur_level = '.'.join(cur_level.split('.')[:-1])
                print("Now considering entire %s theory package"%cur_level)
            elif r[0].lower() == 'c':
                # cancel
                raise UnusableProof(Judgment.theorem_being_proven, self)

class DefinitionExistence(Theorem):
    '''
    For conservative definitions, the unique existence of the 
    Literal(s) with corresponding defining properties must be
    proven effectively as a Theorem.
    '''

    def __init__(self, expr, theory, name, *,
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
        Theorem.__init__(self, expr, theory, name, 
                         _proven_truth=_proven_truth,
                         _requirements=_requirements, 
                         _marked_req_indices=_marked_req_indices)

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        return DefiningProperty(
                None, self.theory, self.name,
                _proven_truth=proven_truth, _requirements=requirements,
                _marked_req_indices=marked_req_indices)

    def step_type(self):
        if self.is_conjecture():
            return 'conjectured existence'
        return 'definition existence'

    def _generate_step_info(self, object_rep_fn):
        # For these purposes, we should use 'definition existence' even 
        # if the status is 'conjectured existence'.
        return 'definition_existence-' + str(self) + ':'

    def _stored_theorem(self):
        from ._theory_storage import StoredDefinitionExistence
        _, hash_id = self.theory._theory_folder_storage('definitions')._retrieve(self)
        return StoredDefinitionExistence(self.theory, self.name,
                                         hash_id=hash_id)

class DefiningProperty(Proof):
    '''
    The proof for a defining property of conservative definition(s)
    is a direct consequence of the DefinitionExistence.
    '''
    def __init__(self, expr, theory, name, *, def_existence,
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
        if not isinstance(theory, Theory):
            raise TypeError("A DefiningProperty 'theory' must be a "
                             "Theory object")
        if not isinstance(name, str):
            raise TypeError("A DefiningProperty 'name' must be a string")
        if not isinstance(def_existence, DefinitionExistence):
            raise TypeError("A DefiningProperty 'def_existence' must be "
                            "a DefinitionExistence")

        self.theory = theory
        self.name = name
        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return
        else:
            Proof.__init__(self, Judgment(expr, frozenset()), 
                           [def_existence.proven_truth])

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        return DefiningProperty(
                None, self.theory, self.name,
                _proven_truth=proven_truth, _requirements=requirements,
                _marked_req_indices=marked_req_indices)

    def step_type(self):
        return 'defining_property'

    def _generate_step_info(self, object_rep_fn):
        return self.step_type() + '-' + str(self) + ':'

    def _storedDefiningProperty(self):
        from ._theory_storage import StoredDefiningProperty
        return StoredDefiningProperty(self.theory, self.name)

    def get_link(self):
        '''
        Return the HTML link to the property definition.
        '''
        return self._storedDefiningProperty().get_def_link()

    def __str__(self):
        return self.theory.name + '.' + self.name

    def used_defining_properties(self):
        return {self}
    
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
    def __init__(self, implication_expr, assumptions=None, *,
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
        from proveit.logic import Implies
        from proveit._core_.expression.composite import is_double
        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            self.implication_truth = _requirements[0]
            self.antecedent_truth = _requirements[1]
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return
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
            assumptions = [
                assumption for assumption in assumptions if (
                        assumption in implication_truth.assumptions or
                        assumption in antecedent_truth.assumptions)]
            # we have what we need; set up the ModusPonens Proof
            num_lit_gen = (implication_truth.num_lit_gen + 
                           antecedent_truth.num_lit_gen)
            consequent_truth = Judgment(
                implication_expr.operands[1], assumptions,
                num_lit_gen=num_lit_gen)
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

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        return ModusPonens(
            None, _proven_truth=proven_truth, _requirements=requirements,
            _marked_req_indices=marked_req_indices)

    def step_type(self):
        return 'modus ponens'


class Deduction(Proof):
    def __init__(self, consequent_truth, antecedent_expr, *,
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
        from proveit import ExprRange
        from proveit.logic import Implies, And
        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            self.consequent_truth = _requirements[0]
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return
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
            num_lit_gen = consequent_truth.num_lit_gen
            if num_lit_gen > 0:
                print("Instantiation with lit gen")
            implication_truth = Judgment(implication_expr, assumptions,
                                         num_lit_gen=num_lit_gen)
            self.consequent_truth = consequent_truth
            Proof.__init__(self, implication_truth, [self.consequent_truth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        return Deduction(
            None, None, _proven_truth=proven_truth,
            _requirements=requirements, _marked_req_indices=marked_req_indices)

    def step_type(self):
        return 'deduction'


class Instantiation(Proof):
    '''
    An Instantiation proof step eliminates some number of nested Forall
    operations and simultaneously replaces Variables with Expressions 
    according to the replacement map (repl_map).  A Variable that is a
    parameter variable of an internal Lambda expression may only be
    relabeled; it will not be replaced with a non-Variable expression
    within the scope of the Lambda expression.

    See Expression.substituted for details regarding the replacement 
    rules.
    '''

    # Map (orig_judgment, mapping, defaults_config) triples to a set 
    # of Instantiations (there may be multiple Instantiations which 
    # use different assumptions)
    instantiations = dict()
    
    # For convenience in figuring out what went wrong, store the last 
    # unsatisfied condition and associate assumptions.
    unsatisfied_condition = None
    condition_assumptions = None
    
    @staticmethod
    def get_instantiation(orig_judgment, num_forall_eliminations,
                          repl_map, equiv_alt_expansions,
                          simplify_only_where_marked,
                          markers_and_marked_expr):
        '''
        Create or retrieve an Instantiation.  If we have performed
        the Instantiation previously, return it; otherwise, create
        it then return it.
        '''
        mapping, mapping_key_order = Instantiation._generate_mapping(
                orig_judgment, repl_map, equiv_alt_expansions)
        mapping_pairs = tuple(
                [(key, mapping[key]) for key in mapping_key_order])
        # Extract default configurationst that are relevant to
        # the instantiation outcome other than the assumptions.
        # (If simplify_with_known_evaluations is True, don't
        # recall or store the instantiation because it will
        # depend upon what is known).
        important_default_attrs = ('auto_simplify', 'preserve_all',
                                   'replacements', 'preserved_exprs')
        important_configs = [getattr(defaults, attr) for attr
                             in important_default_attrs]
        if simplify_only_where_marked:
            important_configs.append(markers_and_marked_expr)
        # Make the replacements and preserved_exprs sets hashable.
        for _k in (2, 3):
            important_configs[_k] = tuple(
                sorted(important_configs[_k], key=lambda expr:hash(expr)))
        important_configs = tuple(important_configs)
        instantiations = Instantiation.instantiations
        key = (orig_judgment, mapping_pairs, important_configs)
        if (key in instantiations and
                not defaults.simplify_with_known_evaluations):
            for inst in instantiations[key]:
                if inst.proven_truth.is_applicable():
                    # Found a known instantiation.  Retrieve it.
                    # We may be using different assumptions than
                    # previously, though, so we might need to derive
                    # side-effects again.
                    inst._derive_side_effects()
                    return inst
        inst = Instantiation(orig_judgment, num_forall_eliminations,
                             repl_map, equiv_alt_expansions,
                             mapping, mapping_key_order,
                             simplify_only_where_marked,
                             markers_and_marked_expr)
        assert inst.mapping == mapping
        #if not defaults.simplify_with_known_evaluations:
        #    Instantiation.instantiations.setdefault(key, set()).add(inst)
        return inst

    @staticmethod
    def _generate_mapping(orig_judgment, repl_map, 
                          equiv_alt_expansions):
        '''
        Generate an appropriate mapping for an instantiation
        as it is to be displayed in a proof.  Lambda map replacements
        are shown in a function form; for example,
            f : x -> g(x)
        converts to
            f(x) : g(x).
        Also, equiv_alt_expansions are absorbed into the mapping
        in an appropriate manner.
        '''
        from proveit import (Function, Lambda, ExprTuple, IndexedVar)
        from proveit._core_.expression.lambda_expr.lambda_expr import (
                get_param_var)
        from proveit._core_.expression.label.var import safe_dummy_var

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
                return var
            return get_param_var(key)
        repl_var_keys = {get_key_var(key): key for key in repl_map.keys()}
        repl_vars = repl_var_keys.keys()
        repl_vars = list(orig_judgment.order_of_appearance(repl_vars))
        # And remove duplicates.
        repl_vars = list(OrderedDict.fromkeys(repl_vars))

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
                    if isinstance(var_range_form, IndexedVar):
                        mapping[var_range_form] = repl_map[var_range_form]
                    else:
                        mapping[var_range_form] = (
                            equiv_alt_expansions[var_range_form])
                    mapping_key_order.append(var_range_form)
        return mapping, mapping_key_order

    
    def __init__(self, orig_judgment, num_forall_eliminations,
                 repl_map, equiv_alt_expansions,
                 mapping, mapping_key_order,
                 simplify_only_where_marked, markers_and_marked_expr, *,
                 _proven_truth=None, _requirements=None,
                 _marked_req_indices=None):
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
        from proveit import (Variable, Lambda, ExprTuple, 
                             ExprRange, IndexedVar)
        from proveit._core_.expression.expr import contained_parameter_vars
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (get_param_var, valid_params, LambdaApplicationError)

        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            self.general_truth = _requirements[0]
            self.mapping = mapping
            self.mapping_key_order = mapping_key_order
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return
        
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
        
        # REVISIT RELABELING ON THE ASSUMPTION SIDE.
        # DO WE WANT TO KEEP THIS FEATURE?
        # IF SO, WE MAY NEED A CHANGE TO MAKE SURE SIDE-EFFECTS
        # ARE PERFORMED UNDER UPDATED ASSUMPTIONS -- THIS IS BROKEN
        # WITH THE "Remember and recall instantiations" COMMIT.
        
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

        if not isinstance(orig_judgment, Judgment):
            raise TypeError("May only 'instantiate' a Judgment")
        if orig_judgment.proof() is None:
            raise UnusableProof(Judgment.theorem_being_proven,
                                orig_judgment)

        # Perform the instantiations, recording requirements.
        requirements = []
        equality_repl_requirements = set()
        try:
            instantiated_expr = Instantiation._instantiated_expr(
                orig_judgment, relabel_params, relabel_param_replacements,
                param_to_num_operand_entries,
                num_forall_eliminations, repl_map,
                equiv_alt_expansions, 
                simplify_only_where_marked, markers_and_marked_expr,
                requirements, equality_repl_requirements)
        except LambdaApplicationError as e:
            raise InstantiationFailure(orig_judgment, repl_map,
                                       defaults.assumptions, str(e))

        # Remove duplicates in the requirements.
        requirements = list(OrderedDict.fromkeys(requirements))
    
        # Remove any unnecessary assumptions (but keep the order
        # that was provided).  Note that some assumptions of
        # requirements may not be in the 'applied_assumptions'
        # if they made use of internal assumptions from a
        # Conditional and can be eliminated.
        applied_assumptions = defaults.assumptions
        assumptions = list(orig_judgment.assumptions)
        for requirement in requirements:
            for assumption in requirement.assumptions:
                if assumption in applied_assumptions:
                    assumptions.append(assumption)
        assumptions = list(OrderedDict.fromkeys(assumptions))

        self.mapping_key_order = mapping_key_order
        self.mapping = mapping
        # Make the 'original judgment' be the 1st requirement.
        requirements.insert(0, orig_judgment)
        num_lit_gen = sum(requirement.num_lit_gen for requirement
                          in requirements)
        instantiated_truth = Judgment(instantiated_expr, assumptions,
                                      num_lit_gen=num_lit_gen)
        # Mark the requirements that are "equality replacements".
        marked_req_indices = set()
        for k, req in enumerate(requirements):
            if req in equality_repl_requirements:
                marked_req_indices.add(k)
        self.general_truth = orig_judgment
        Proof.__init__(self, instantiated_truth, requirements,
                       marked_req_indices)

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        inst = Instantiation(
            None, None, None, None, self.mapping, self.mapping_key_order, 
            None, None, _proven_truth=proven_truth, _requirements=requirements,
            _marked_req_indices=marked_req_indices)
        return inst

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
                           simplify_only_where_marked, 
                           markers_and_marked_expr,
                           requirements, equality_repl_requirements):
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
                                       defaults.assumptions, msg)
        
        def instantiate(expr, _simplify_only_where_marked=False,
                        _markers_and_marked_expr=None):
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
                    auto_simplify_top_level=False,
                    simplify_only_where_marked=_simplify_only_where_marked,
                    markers_and_marked_expr=_markers_and_marked_expr)

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
                        if subbed_cond.proven():
                            # If the full condition conjunction is known
                            # to be true, we'll just use that as the
                            # requirement and be done with it.
                            requirements.append(subbed_cond.prove())
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
                            requirements.append(subbed_cond.prove())
                        except ProofFailure:
                            Instantiation.unsatisfied_condition = subbed_cond
                            Instantiation.condition_assumptions = tuple(
                                    defaults.assumptions)
                            raise_failure(
                                    'Unsatisfied condition: %s. '
                                    'For debugging purposes, this is '
                                    'accessible via '
                                    'Instantiation.unsatisfied_condition '
                                    'with applicable assumptions in '
                                    'Instantiation.condition_assumptions.'
                                    % str(subbed_cond))

        # Make final instantiations in the inner instance expression.
        # Add to the lambda-application parameters anything that has
        # not yet been used
        # simplify_only_where_marked = False # TEMPORARILY DISABLING THIS FEATURE
        return instantiate(expr, simplify_only_where_marked,
                           markers_and_marked_expr)


class Generalization(Proof):
    def __init__(
            self, instance_truth, new_forall_param_lists,
            new_conditions=tuple(), new_antecedent=None, *, 
            _proven_truth=None, _requirements=None, _marked_req_indices=None):
        '''
        A Generalization step wraps a Judgment (instance_truth) in one 
        or more Forall operations.  The number of Forall operations
        introduced is the number of lists in new_forall_var_lists.
        The conditions are introduced in the order they are given at 
        the outermost level that is applicable.  For example, if 
        new_forall_param_lists is [[x, y], z]  and the new conditions 
        are f(x, y) and g(y, z) and h(z), this will prove a statement 
        of the form:
            forall_{x, y ∈ ℤ | f(x, y)} forall_{z | g(y, z), h(z)} ...
        
        In addition to ordinary Variable generalization, this also
        deals with Literal generalization.  If, for any of the new
        parameter variables, the Variable is not in contained in
        the instance_truth but a corresponding Literal (with the same
        formatting, see Literal.var_to_lits) is contained, then a
        Literal generalization will be attempted in which axioms or
        theorems corresponding to new_conditions may be eliminated.
        As a very simple example for illustration, if we prove
            ⊢ _a + _b = 10
        Using the following axioms:
            ⊢ _a = 2
            ⊢ _b = 8
        Then, through Literal generalization assuming _a and _b
        have the same formatting as a and b, we can prove:
            ⊢ ∀_{a, b | a=2, b=8} a + b = 10
        and eliminate the axioms involing _a and _b.
        
        Alternative to a condition, a new_antecedent may be provided
        which may be useful for formatting purposes.  For example,
            ⊢ ∀_{a, b | a=2} (b = 8) => a + b = 1 
        '''
        from proveit import Judgment
        from proveit.logic import Implies
        from proveit._core_.expression.expr import (
                used_literals, free_vars)
        from proveit._core_.expression.label.literal import (
                Variable, Literal)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (get_param_var)
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        from proveit.logic import Forall
        if _proven_truth is not None:
            # Via _regenerate_proof_object:
            self.instance_truth = _requirements[0]
            Proof.__init__(self, _proven_truth, _requirements,
                           _marked_req_indices)
            return

        if not isinstance(instance_truth, Judgment):
            raise GeneralizationFailure(
                None, [], 'May only generalize a Judgment instance')
        
        # Let's check if this is a job for Literal generalization
        # where we convert Literals to Variables.
        instance_expr = instance_truth.expr
        instance_literals = used_literals(instance_expr)
        var_to_instance_literal = {lit.as_variable():lit for lit
                                   in instance_literals}
        generalized_literals = set()
        converted_param_lists = []
        for param_list in new_forall_param_lists:
            converted_param_list = []
            for param in param_list:
                if isinstance(param, Literal):
                    # Generalized this Literal
                    generalized_literals.add(param)
                    converted_param_list.append(param.as_variable())
                elif param in var_to_instance_literal:
                    # Assume the Literal that is contained
                    # in the instance and corresponds with
                    # the parameter Variable should be
                    # generalized as a Literal.
                    generalized_literals.add(
                        var_to_instance_literal[param])
                    converted_param_list.append(param)
                else:
                    converted_param_list.append(param)
            converted_param_lists.append(converted_param_list)
        # With literals converted to variables.
        new_forall_param_lists = converted_param_lists

        if isinstance(new_conditions, ExprTuple):
            new_conditions = list(new_conditions.entries)

        assumptions = list(instance_truth.assumptions)
        instance_expr = instance_truth.expr
        if len(generalized_literals) > 0:
            # Literal generalization convert literals to variables.
            instance_expr = instance_expr.literals_as_variables(
                    *generalized_literals)
            if new_antecedent is not None:
                new_antecedent = new_antecedent.literals_as_variables(
                    *generalized_literals)
            new_conditions = [new_condition
                              .literals_as_variables(*generalized_literals)
                              for new_condition in new_conditions]
            assumptions = [assumption
                           .literals_as_variables(*generalized_literals)
                              for assumption in assumptions]
        
        # The assumptions required for the generalization are the
        # assumptions of the original Judgment minus the all of the
        # new conditions (including those implied by the new domain).
        prev_default_assumptions = defaults.assumptions
        # these assumptions will be used for deriving any side-effects
        defaults.assumptions = assumptions
        if new_antecedent is not None:
            # An antecedent serves the role of a condition
            # but is placed in an implication instead of a
            # in a Conditional.
            instance_expr = Implies(new_antecedent, 
                                    instance_expr)
        try:
            remaining_conditions = list(new_conditions)
            expr = instance_expr
            introduced_forall_vars = set()
            for k, new_forall_params in enumerate(
                    reversed(new_forall_param_lists)):
                new_forall_vars = [get_param_var(parameter)
                                   for parameter in new_forall_params]
                introduced_forall_vars |= set(new_forall_vars)
                _conditions = []
                if k == len(new_forall_param_lists) - 1:
                    # the final introduced Forall operation must use all of the
                    # remaining conditions
                    _conditions = remaining_conditions
                else:
                    # use all applicable conditions in the supplied order
                    condition_applicability = \
                        [not free_vars(remaining_cond).isdisjoint(
                            new_forall_vars)
                         for remaining_cond in remaining_conditions]
                    _conditions = \
                        [remaining_cond for applicable, remaining_cond
                         in zip(condition_applicability, remaining_conditions)
                         if applicable]
                    remaining_conditions = \
                        [remaining_cond for applicable, remaining_cond
                         in zip(condition_applicability, remaining_conditions)
                         if not applicable]
                # new conditions can eliminate corresponding assumptions
                _conditions_set = set(_conditions)
                assumptions = [assumption for assumption in assumptions
                               if assumption not in _conditions_set]
                # create the new generalized expression
                generalized_expr = Forall(
                    instance_param_or_params=new_forall_params,
                    instance_expr=expr, conditions=_conditions)
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
                        'Cannot generalize using assumptions that involve '
                        'any of the new forall variables (except as '
                        'assumptions are eliminated via conditions or '
                        'domains)')
            num_lit_gen = instance_truth.num_lit_gen
            if len(generalized_literals) > 0:
                num_lit_gen += 1
            generalized_truth = Judgment(generalized_expr, assumptions,
                                         num_lit_gen=num_lit_gen)
            self.instance_truth = instance_truth
            self.new_forall_vars = new_forall_vars
            if new_antecedent is not None:
                new_conditions.append(new_antecedent)
            self.new_conditions = tuple(new_conditions)

            self.generalized_literals = frozenset(generalized_literals)
            if len(generalized_literals) > 0:
                # We are generalizing Literals.  We will eliminate
                # requirements masked by conditions after Literals
                # convert to Variables and make sure there are no
                # other requirements that use these Literals.
                eliminated_proof_steps = []
                eliminated_axioms = []
                eliminated_defining_properties = []
                eliminated_theorems = []
                self._append_eliminated_requirements_and_check_violation(
                        instance_truth, new_conditions,
                        generalized_expr, eliminated_proof_steps,
                        eliminated_axioms, eliminated_defining_properties,
                        eliminated_theorems)
                instance_proof = instance_truth.proof()
                self._eliminated_proof_steps = frozenset(
                    eliminated_proof_steps).union(
                        instance_proof.eliminated_proof_steps())
                self._eliminated_axioms = frozenset(eliminated_axioms).union(
                    instance_proof.eliminated_axioms())
                self._eliminated_defining_properties = (
                    frozenset(eliminated_defining_properties).union(
                        instance_proof.eliminated_defining_properties()))
                self._eliminated_theorems = (
                    frozenset(eliminated_theorems).union(
                        instance_proof.eliminated_theorems()))

            Proof.__init__(self, generalized_truth, [self.instance_truth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def _regenerate_proof_object(self, proven_truth, requirements,
                                 marked_req_indices):
        gen = Generalization(
            None, None, _proven_truth=proven_truth, _requirements=requirements,
            _marked_req_indices=marked_req_indices)
        gen.new_forall_vars = self.new_forall_vars
        gen.new_conditions = self.new_conditions
        gen.generalized_literals = self.generalized_literals
        gen._eliminated_proof_steps = self._eliminated_proof_steps
        gen._eliminated_axioms = self._eliminated_axioms
        gen._eliminated_defining_properties = self._eliminated_defining_properties
        gen._eliminated_theorems = self._eliminated_theorems
        return gen

    def _append_eliminated_requirements_and_check_violation(
            self, instance_truth, new_conditions,
            generalized_expr, eliminated_proof_steps,
            eliminated_axioms, eliminated_defining_properties,
            eliminated_theorems):
        '''
        There is literal generalization going on.  Convert the
        new conditions to forms using the literals in place
        of corresponding variables, search through the
        instance_truth requirements and the axioms/theorems they
        depend upon up until, but not including, any of these
        transformed new conditions and make sure none of the
        rest involves any of the literals being generalized.
        Find the axioms/theorems corresponding to the new 
        conditions and record them as axioms/theorems that are
        explicitly not needed for this particular proof.
        '''
        from proveit import used_literals
        from ._theory_storage import StoredTheorem
        generalized_literals = self.generalized_literals
        converted_conditions = {
                condition.variables_as_literals(*generalized_literals)
                for condition in new_conditions}

        def check_axiom_or_unproven_theorem(proof):
            '''
            When encountering an axiom or unproven theorem that
            is not being eliminated, it must not contain any of
            the literals being generalized.
            '''
            proof_expr = proof.proven_truth.expr
            if not used_literals(proof_expr).isdisjoint(
                    generalized_literals):
                # A non-eliminated Axiom or unproven Theorem that
                # uses one of the literals we are trying the
                # generalize: NO BUENO!
                raise LiteralGeneralizationFailure(
                    generalized_expr, defaults.assumptions,
                    "%s: %s is an an Axiom or unproven Theorem, "
                    "not eliminated via a condition, yet "
                    "contains one or more of the literals we "
                    "are attempting to generalize: %s"
                    %(str(proof), proof.proven_truth, 
                      generalized_literals))

        # First, use a breadth-first search through proof requirements
        # to determine all of the eliminated requirements and direct
        # axioms/theorems (matching converted conditions) obtain all 
        # of the required theorems (that aren't directly eliminated).
        instance_proof = instance_truth.proof()
        to_process = deque([instance_proof])
        instance_eliminated_proof_steps = (
            instance_proof.eliminated_proof_steps())
        # Exclude these Axiom/Theorem names because they are 
        # eliminated in the proof of the instance expression.
        excluded_names = {str(ax) for ax in 
                          instance_proof.eliminated_axioms()}
        excluded_names.update({str(prop) for prop in 
                               instance_proof.eliminated_defining_properties()})
        excluded_names.update({str(thm) for thm in 
                               instance_proof.eliminated_theorems()})
        required_theorems = set()
        while len(to_process) > 0:
            proof = to_process.popleft()
            if proof in instance_eliminated_proof_steps:
                # This proof step is eliminated in the instance proof.
                continue
            proof_expr = proof.proven_truth.expr
            proof_is_axiom = isinstance(proof, Axiom)
            proof_is_defining_property = isinstance(proof, DefiningProperty)
            proof_is_theorem = isinstance(proof, Theorem)
            if proof_is_axiom or proof_is_theorem:
                if str(proof) in excluded_names:
                    # Eliminated in the instance proof.
                    continue
            if (len(proof.proven_truth.assumptions) == 0 and
                   proof_expr in converted_conditions):
                if proof_is_axiom:
                    # Axiom corresponding to a condition -- it is
                    # eliminated.
                    eliminated_axioms.append(proof)
                elif proof_is_defining_property:
                    # DefiningProperty corresonding to a condition -- 
                    # it is eliminated.
                    eliminated_defining_properties.append(proof)
                elif proof_is_theorem:
                    # Theorem corresonding to a condition -- it is
                    # eliminated.
                    eliminated_theorems.append(proof)
                else:
                    # Eliminate this proof requirement which
                    # corresponds to one of the new conditions.
                    eliminated_proof_steps.append(proof)
                # No need to go any further along this path.
                continue
            if proof_is_axiom or (proof_is_theorem and  
                                  not proof.has_proof()):
                # An Axiom or unproven Threorem.
                check_axiom_or_unproven_theorem(proof)
                continue
            if proof_is_theorem:
                required_theorems.add(proof)
            else:
                # Continue search with the required proofs of this
                # one.
                to_process.extend(proof.required_proofs)

        # Search through the requirements of the required theorems
        # for indirectly eliminated axioms/theorems.
        required_axioms, required_def_props, required_deadend_theorems, _ = (
            StoredTheorem.requirements_of_theorems(
                required_theorems, 
                dead_end_theorem_exprs=converted_conditions,
                excluded_names=excluded_names))
        # Disregard conservative definitions.
        required_axioms, required_def_props, required_deadend_theorems, _ = (
                StoredTheorem._extract_conservative_definitions(
                        instance_truth.expr, required_axioms,
                        required_def_props, required_deadend_theorems))
        for required_axiom in required_axioms:
            if required_axiom.proven_truth.expr in converted_conditions:
                eliminated_axioms.append(required_axiom)
            else:
                check_axiom_or_unproven_theorem(required_axiom)
        for required_def_prop in required_def_props:
            if required_def_prop.proven_truth.expr in converted_conditions:
                eliminated_defining_properties.append(required_def_prop)
            else:
                check_axiom_or_unproven_theorem(required_axiom)
        for required_theorem in required_deadend_theorems:
            if required_theorem.proven_truth.expr in converted_conditions:
                eliminated_theorems.append(required_theorem)
            else:
                assert not required_theorem.has_proof(), (
                    "If it had a proof and doesn't correspond with "
                    "a converted condition, it shouldn't have been "
                    "returned by StoredTheorem.all_requirements")
                check_axiom_or_unproven_theorem(required_theorem)

    
    def step_type(self):
        if len(self.generalized_literals) > 0:
            return 'literal generalization'
        return 'generalization'

    @staticmethod
    def _checkGeneralization(generalized_expr, instance_expr):
        '''
        Make sure the generalized_expr is a proper generalization of the
        instance_expr.
        '''
        from proveit import Lambda, Conditional
        from proveit.logic import Forall, Implies
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
            if isinstance(expr, Implies):
                # Dig into the implication consequent.
                # The antecedent only weakens the statement so
                # it doesn't matter what it is.
                expr = expr.consquent
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
            # axiom-theory.name or theorem-theory.name
            self.step_type_str, full_name = step_info.split('-', 1)
            assert self.step_type_str in (
                'axiom', 'defining_property', 'definition_existence', 
                'theorem')
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
        from ._theory_storage import (axiom_specification_link, 
                                      theorem_proof_link)
        if self.step_type_str == 'axiom':
            return axiom_specification_link(self.theory, self.name)
        elif self.step_type_str == 'theorem':
            return theorem_proof_link(self.theory, self.name)
        elif self.step_type_str == 'definition_existence':
            return theorem_proof_link(self.theory, self.name)
        else:
            return self.theory_folder_storage.proof_notebook(self)

    def _single_mapping(self, *args):
        return Instantiation._single_mapping(self, *args)

    def _mapping(self, *args):
        return Instantiation._mapping(self, *args)

    def enumerated_proof_steps(self):
        return Proof.enumerated_proof_steps(self)

    def is_possibly_usable(self):
        return True

    def explicitly_allowed(self):
        return True

class ProofFailure(Exception):
    def __init__(self, expr, assumptions, message):
        self.expr = expr
        self.message = message
        self.assumptions = assumptions
        self.automation = defaults.conclude_automation

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
        self.assumptions = tuple(defaults.assumptions)
    
    def __str__(self):
        return "Prerequisites not met while assuming %s: %s"%(
                self.assumptions, self.msg)

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

class LiteralGeneralizationFailure(GeneralizationFailure):
    def __init__(self, expr, assumptions, message):
        GeneralizationFailure.__init__(self, expr, assumptions, message)


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
