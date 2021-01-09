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

    # Map each Proof to the first instantiation of it that was created (noting that
    # multiple Proof objects can represent the same Proof and will have the same hash value).
    # Using this, internal references (between Judgments and Proofs) unique .
    unique_proofs = dict()

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information in
        the Proof jurisdiction.
        '''
        Proof.unique_proofs.clear()
        Assumption.all_assumptions.clear()
        Theorem.all_theorems.clear()
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

            # Is this a usable Proof?  An unusable proof occurs when trying to prove a Theorem
            # that must explicitly presume Theorems that are not fully known in order to
            # avoid circular logic.  They can also be manually introduced via
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

        # reference this unchanging data of the unique 'meaning' data
        self._meaning_id = self._meaning_data._unique_id

        # reference this data of the unique 'meaning' data, but note that these
        # are subject to change (as proofs are disabled and as new dependencies
        # are added).
        self.required_proofs = self._meaning_data.required_proofs
        self._dependents = self._meaning_data._dependents

        all_required_proofs = self.all_required_proofs()
        all_required_truths = {
            required_proof.proven_truth for required_proof in all_required_proofs if required_proof is not self}
        original_proof = self.proven_truth not in all_required_truths

        if original_proof:
            # As long as this is not a useless self-dependent proof (a proof that depends upon
            # a different proof of the same truth which should never actually get used),
            # track the dependencies of required proofs so they can be updated appropriated if there are
            # changes due to proof disabling.
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
            if not required_proof.is_usable():
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
            self._setUsability()
        # this new proof may be the first proof, make an old one obselete, or be born obsolete itself.
        #had_previous_proof = (proven_truth.proof() is not None and proven_truth.is_usable())
        proven_truth._addProof(self)
        if requiring_unusable_proof:
            # Raise an UnusableProof exception when an attempt is made
            # to use an "unusable" theorem directly or indirectly.
            raise UnusableProof(
                Judgment.theorem_being_proven,
                self._meaning_data._unusable_proof)
        if proven_truth.proof() == self and self.is_usable(
        ):  # don't bother with side effects if this proof was born obsolete or unusable
            # May derive any side-effects that are obvious consequences arising from this truth
            # (if it has not already been processed):
            proven_truth.derive_side_effects(defaults.assumptions)

    def _updateDependencies(self, newproof):
        '''
        Swap out this oldproof for the newproof in all dependents and update their num_steps
        and usability status.
        '''
        oldproof = self
        for dependent in oldproof._dependents:
            revised_dependent = False
            i = 0
            try:
                while True:
                    i = dependent.required_proofs.index(oldproof, i)
                    dependent.required_proofs[i] = newproof
                    revised_dependent = True
            except ValueError:
                pass
            assert revised_dependent, "Incorrect dependency relationship"
            newproof._dependents.add(dependent)
            if all(required_proof.is_usable()
                   for required_proof in dependent.required_proofs):
                dependent._meaning_data._unusable_proof = None  # it is usable again
                dependent._meaning_data.num_steps = len(
                    dependent.all_required_proofs())
                dependent.proven_truth._addProof(
                    dependent)  # add it back as an option

    def _setUsability(self):
        pass  # overloaded for the Theorem type Proof

    def _generate_unique_rep(self, object_rep_fn):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        # Internally, for self._meaning_rep and self._style_rep, we will use self.required_truths in the unique representation
        # and the proofs are subject to change (if anything is disabled).
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
        Overridden by Specialization which also needs to including the mapping information
        and uses the given function to obtain representations of sub-Object.
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
        # Get the set of all dependents via breadth-first search
        all_dependents = set()
        to_process = [self]
        while len(to_process) > 0:
            dependent_proof = to_process.pop()
            if dependent_proof not in all_dependents:
                all_dependents.add(dependent_proof)
                if dependent_proof.proven_truth.proof() == dependent_proof:
                    # include the sub-dependents iff this dependent is actually
                    # in use
                    to_process.extend(dependent_proof._dependents)

        # Disable all dependents
        for dependent_proof in all_dependents:
            dependent_proof._meaning_data._unusable_proof = self
            dependent_proof.proven_truth._discardProof(dependent_proof)

        # Check if alternate usable proofs are available for the proofs that we disabled.
        # Make multiple passes to ensure new possibilities and best options
        # fully propagate.
        continue_revisions = True
        while continue_revisions:
            continue_revisions = False
            for dependent_proof in all_dependents:
                if dependent_proof.proven_truth.proof() == dependent_proof:
                    # Check for an alternate to this disabled dependent proof.
                    if dependent_proof.proven_truth._reviseProof():
                        continue_revisions = True

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
        return self._meaning_data.num_steps

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

    def all_required_proofs(self):
        '''
        Returns the set of directly or indirectly required proofs.
        '''
        sub_proof_sets = [required_proof.all_required_proofs()
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
            if proof.step_type() == 'axiom' or proof.step_type() == 'theorem':
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
            preexisting.proven_truth.derive_side_effects(assumptions)
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
        # Note that _setUsability will be called within Proof.__init__
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
        for theorem in Theorem.all_theorems:
            theorem._setUsability()

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

    def all_used_theorem_names(self):
        '''
        Returns the set of theorems used to prove the given theorem, directly
        or indirectly.
        '''
        return self._stored_theorem().all_used_theorem_names()

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

    def _setUsability(self):
        '''
        Sets the '_unusable_proof' attribute to disable the
        theorem if some theorem is being proven and this
        theorem is not presumed or is an alternate proof for the
        same theorem.  Also, if it is presumed, ensure the logic
        is not circular.  Generally, this is preventing circular
        logic.  This applies when a proof has begun
        (see Judgment.begin_proof in judgment.py).
        When Judgment.theorem_being_proven is None, all Theorems are allowed.
        Otherwise only Theorems named in the Judgment.presuming_theorem_names set
        or contained within any of the Judgment.presuming_theories
        (i.e., theory) are allowed.
        '''
        #from proveit.certify import is_fully_proven
        if Judgment.theorem_being_proven is None:
            # Nothing being proven, so all Theorems are usable
            self._meaning_data._unusable_proof = None
            return
        legitimately_presumed = False
        stored_theorem = self._stored_theorem()
        theorem_being_proven_str = str(Judgment.theorem_being_proven)
        if self.proven_truth == Judgment.theorem_being_proven.proven_truth:
            # Note that two differently-named theorems for the same thing may exists in
            # order to show an alternate proof.  In that case, we want to disable
            # the other alternates as well so we will be sure to generate the
            # new proof.
            self.disable()
            return
        else:
            name_and_containing_theories = list(
                self.theorem_name_and_containing_theories())
            exclusions = Judgment.presuming_theorem_and_theory_exclusions
            if exclusions.isdisjoint(name_and_containing_theories):
                presumptions = Judgment.presumed_theorems_and_theories
                presumed = not presumptions.isdisjoint(
                    name_and_containing_theories)
            else:
                presumed = False
            if presumed:
                # This Theorem is being presumed specifically, or a theory in which it is contained is presumed.
                # Presumption via theory (a.k.a. prefix) is contingent upon not having a mutual presumption
                # (that is, some theorem T can presume everything in another theory except for theorems
                # that presume T or, if proven, depend upon T).
                # When Theorem-specific presumptions are mutual, a CircularLogic error is raised when either
                # is being proven.
                # check the "presuming information, recursively, for circular
                # logic.
                my_possible_dependents, _ = stored_theorem.get_presumptions_and_exclusions()
                # If this theorem has a proof, include all dependent theorems as
                # presumed (this may have been presumed via theory, so this can contain
                # more information than the specifically presumed theorems).
                if stored_theorem.has_proof():
                    my_possible_dependents.update(
                        stored_theorem.all_used_theorem_names())
                if theorem_being_proven_str in my_possible_dependents:
                    if str(self) in Judgment.presumed_theorems_and_theories:
                        # Theorem-specific presumption or dependency is
                        # mutual.  Raise a CircularLogic error.
                        raise CircularLogic(
                            Judgment.theorem_being_proven, self)
                    # We must exclude this theorem implicitly to
                    # avoid a circular dependency.
                    print("%s is being implicitly excluded as a "
                          "presumption to avoid a Circular dependency."
                          % str(self))
                else:
                    legitimately_presumed = True
        if not legitimately_presumed:
            # This Theorem is not usable during the proof (if it is needed, it must be
            # presumed or fully proven).  Propagate this fact to all
            # dependents.
            self.disable()


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
                implication_truth = implication_expr.prove(assumptions)
            except ProofFailure:
                raise ModusPonensFailure(
                    implication_expr.operands[1],
                    assumptions,
                    'Implication, %s, is not proven' %
                    str(implication_expr))
            try:
                # Must prove the antecedent under the given assumptions.
                antecedent_truth = implication_expr.operands[0].prove(
                    assumptions)
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
        Create the instantiation+instantiation proof step that eliminates
        some number of nested Forall operations (instantiation) and
        simultaneously replaces Variables with Expressions (instantiation)
        according to the replacement map (repl_map). A Variable that is
        a parameter variable of an internal Lambda expression may only
        be relabeled; it will not be replaced with a non-Variable expression
        within the scop of the Lambda expression.

        See Expression.substituted for details regarding the replacement rules.
        '''
        from proveit import (Expression, Function, Lambda, ExprRange,
                             ExprTuple)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (get_param_var, LambdaApplicationError)

        # Prepare the 'parameters' and 'operands' for a lambda map
        # application (beta reduction) to perform the replacements.
        parameters = []
        for key, repl in repl_map.items():
            if isinstance(repl, set):
                # When the replacement is a set, it indicates a set
                # of possible ways to expand a range of variables.
                # For the current purpose, skip these instances.
                continue
            if not isinstance(repl, Expression):
                raise TypeError("Replacement %s is of type %s and not "
                                "an 'Expression' object"
                                % (repl, repl.__class__))
            if isinstance(key, ExprTuple):
                # If the key is an ExprTuple, it must either be a
                # range (or range of ranges, etc.) of an indexed variable
                # for a full expansion, or it is an "equivalent alternative
                # expansion".
                # Should already have been checked in
                # Judgment.instantiate:
                try:
                    for param_entry in key:
                        get_param_var(param_entry)
                except TypeError as e:
                    assert False, ("Should have been checked in 'instantiate' "
                                   "method:\n%s" % str(e))
                parameters.append(key[0])
            else:
                parameters.append(key)
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

            # The "original" Judgment is the first "requirement truth" for
            # this derivation step.
            orig_subbed_assumptions = []
            requirements = []
            equality_repl_requirements = set()

            # Make possible substitutions in the "original" Judgment
            # assumption.
            operands = []
            for parameter in parameters:
                if (ExprTuple(parameter) in repl_map):
                    # Yield the entries for the replacement of the
                    # ExprTuple of the parameter.
                    for entry in repl_map[ExprTuple(parameter)]:
                        operands.append(entry)
                else:
                    operands.append(repl_map[parameter])
            for assumption in orig_judgment.assumptions:
                subbed_assumption = Lambda._apply(
                    parameters, assumption, *operands,
                    allow_relabeling=False,
                    equiv_alt_expansions=equiv_alt_expansions,
                    assumptions=assumptions, requirements=requirements,
                    equality_repl_requirements=equality_repl_requirements)
                if isinstance(assumption, ExprRange):
                    # An iteration of assumptions to expand.
                    orig_subbed_assumptions.extend(subbed_assumption)
                else:
                    orig_subbed_assumptions.append(subbed_assumption)

            # Automatically use the assumptions of the
            # original_judgment plus the assumptions that were
            # provided.
            assumptions = tuple(orig_subbed_assumptions) + assumptions
            # Eliminate duplicates.
            assumptions = tuple(OrderedDict.fromkeys(assumptions))
            # Make this the new default (for side-effects).
            defaults.assumptions = assumptions

            instantiated_expr = \
                Instantiation._instantiated_expr(
                    orig_judgment, num_forall_eliminations,
                    parameters, repl_map, equiv_alt_expansions,
                    assumptions, requirements,
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

            # Sort the replaced variables in order of their appearance
            # in the original Judgment.
            def get_key_var(key):
                if isinstance(key, ExprTuple):
                    assert key.num_entries() >= 1
                    return get_param_var(key[0])
                return get_param_var(key)
            repl_var_keys = {get_key_var(key): key for key in repl_map.keys()}
            repl_vars = repl_var_keys.keys()
            repl_vars = list(orig_judgment.order_of_appearance(repl_vars))
            # And remove duplicates.
            repl_vars = list(OrderedDict.fromkeys(repl_vars))

            # Map variables to sets of tuples that represent the
            # same range of indexing for equivalent alternative
            # expansions.  For example,
            #   {x_1, ..., x_{n+1}, x_1, ..., x_n, x_{n+1}}.
            var_range_forms = dict()
            for var_range_form, expansion in equiv_alt_expansions.items():
                var = get_param_var(var_range_form[0])
                var_range_forms.setdefault(var, set()).add(var_range_form)

            # We have what we need; set up the Instantiation Proof
            self.orig_judgment = orig_judgment
            # Exclude anything in the repl_map that does not appear in
            # the original Judgment:
            mapping = dict()
            mapping_key_order = []

            def var_range_form_sort(var_tuple):
                # For sorting equivalent ExprTuples of indexed
                # variables (e.g., {(x_1, ..., x_{n+1}),
                #                   (x_1, ..., x_n, x_{n+1})})
                # put ones with the fewest number of entries first
                # but break ties arbitrarily via the "meaning id".
                return (var_tuple.num_entries(), var_tuple._meaning_id)
            for var in repl_vars:
                if var in repl_map:
                    # The variable itself is in the replacement map.
                    replacement = repl_map[var]
                    if isinstance(replacement, Lambda):
                        # If the replacement is a Lambda, convert it
                        # to a Function mapping form.
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
    def _get_nested_params(expr, num_nested_foralls):
        '''
        Assuming the given 'expr' has at least 'num_nested_foralls'
        levels of directly nested universal quantifications,
        return the list of parameters for these quantifications.
        '''
        from proveit import Lambda, Conditional
        from proveit.logic import Forall
        parameters = []
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
            parameters.extend(lambda_expr.parameters)
            expr = lambda_expr.body
            if isinstance(expr, Conditional):
                expr = expr.value
        return parameters

    @staticmethod
    def _instantiated_expr(original_judgment, num_forall_eliminations,
                           instantiation_params, repl_map,
                           equiv_alt_expansions,
                           assumptions, requirements,
                           equality_repl_requirements):
        '''
        Return the instantiated version of the right side of the
        original_judgment.  The assumptions on the left side of
        the turnstile are treated in Instantiation.__init__.

        Eliminates the specified number of Forall operations,
        substituting all  of the corresponding instance variables
        according to repl_map.
        '''
        from proveit import (Lambda, Conditional, ExprTuple, ExprRange)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            get_param_var
        from proveit.logic import Forall, And

        # Eliminate the desired number of Forall operations and extract
        # appropriately mapped conditions.
        expr = original_judgment.expr

        def raise_failure(msg):
            raise InstantiationFailure(original_judgment, repl_map,
                                       assumptions, msg)
        instantiation_param_vars = [get_param_var(param) for param
                                    in instantiation_params]
        # When an implicit range of indexed variables becomes explicit,
        # map this correspondence, e.g., 'x' to 'x_1, ..., x_n' when
        # eliminated \forall_{x_1, ..., x_n}.
        explicit_ranges = dict()

        def instantiate(expr, exclusion=None):
            '''
            Instantiate the given expression by applying an
            ad-hoc Lambda mapping with parameters from the
            instantiation_params and operands extracted from the
            current repl_map.  If an exclusion is provided, skip
            parameters whose variable is the exclusion.
            '''
            params = []
            operands = []
            for param, param_var in zip(instantiation_params,
                                        instantiation_param_vars):
                if param_var == exclusion:
                    continue  # skip the 'exclusion'
                if isinstance(param, ExprRange):
                    # An ExprRange parameter should have a tuple
                    # replacement for its tuple form.
                    for entry in repl_map[ExprTuple(param)]:
                        operands.append(entry)
                elif param_var in explicit_ranges:
                    # When an implicit range is mapped to an
                    # explicit one, a variable instantiation
                    # should be replaced by the corresponding range
                    # of variables.
                    # For example
                    #   x : (x_1, ..., x_n)
                    # which may be introduced after eliminating a
                    #   \forall_{x_1, ..., x_n} ...
                    # universal quantifier.
                    param = explicit_ranges[param_var]
                    for entry in repl_map[ExprTuple(param)]:
                        operands.append(entry)
                else:
                    operands.append(repl_map[param])
                params.append(param)
            if len(params) == 0:
                return expr
            return Lambda._apply(
                params, expr, *operands, allow_relabeling=True,
                equiv_alt_expansions=equiv_alt_expansions,
                assumptions=assumptions, requirements=requirements,
                equality_repl_requirements=equality_repl_requirements)

        remaining_forall_eliminations = num_forall_eliminations
        while remaining_forall_eliminations > 0:
            remaining_forall_eliminations -= 1
            assert isinstance(expr, Forall)
            lambda_expr = expr.operand
            assert isinstance(lambda_expr, Lambda)
            expr = lambda_expr.body

            # Check for implicit variable range substitutions
            # that need to be made explicit.  For example,
            # if we have an instantiation for 'x' that is an ExprTuple
            # and 'x' is universally quantified over a range here
            # (e.g., x_1, ..., x_n), then we will record the
            # correspondence (e.g., x : x_1, ..., x_n) in
            # `explicit_ranges` (used when generating parameters
            # for ad-hoc Lambda expressions) and update
            # repl_map to record the assignments.  For example,
            # x : {(x_1, ..., x_n)}
            # (x_1, ..., x_n) : <the-actual-replacement>
            for param in lambda_expr.parameters:
                if isinstance(param, ExprRange):
                    param_var = get_param_var(param)
                    param_var_repl = repl_map.get(param_var, None)
                    if isinstance(param_var_repl, ExprTuple):
                        subbed_param = instantiate(param, exclusion=param_var)
                        if subbed_param not in repl_map:
                            subbed_param_tuple = ExprTuple(subbed_param)
                            if (subbed_param_tuple in repl_map and
                                    repl_map[subbed_param_tuple] !=
                                    param_var_repl):
                                raise_failure("Inconsistent assignment of "
                                              "%s: %s, from instantiation of "
                                              "%s, versus %s."
                                              % (subbed_param_tuple,
                                                 param_var_repl, param_var,
                                                 repl_map[subbed_param_tuple]))
                            explicit_ranges[param_var] = subbed_param
                            repl_map[subbed_param_tuple] = param_var_repl

            # If there is a condition of the universal quantifier
            # being eliminated, produce the instantiated condition,
            # prove that this is satisfied and add it as "requirements".
            # When there is a conjunction of multiple conditions,
            # separate out a requirement for each individual condition
            # (the operands of the conjunction).
            if isinstance(expr, Conditional):
                condition = expr.condition
                expr = expr.value

                # Instantiate the condition.
                subbed_cond = instantiate(condition)
                if isinstance(subbed_cond, And):
                    # It is important to deal with a conjunction
                    # condition in this implicit manner here or we would
                    # have a chicken/egg infinite recursion problem.
                    # That is, we have to split up a conjunction into
                    # multiple requirements at some point, so we do it
                    # here.
                    if subbed_cond.proven(assumptions):
                        # If the full condition conjunction is known
                        # to be true, we'll just use that as the
                        # requirement and be done with it.
                        requirements.append(subbed_cond.prove(assumptions))
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
                        defaults.debug = (subbed_cond, assumptions)
                    try:
                        requirements.append(subbed_cond.prove(assumptions))
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
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (get_param_var, _guaranteed_to_be_independent)
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
                        [not _guaranteed_to_be_independent(remaining_cond,
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
                if not _guaranteed_to_be_independent(
                        assumption, introduced_forall_vars):
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
        return 'generalizaton'

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
            [theory.get_show_proof(obj_id.rstrip('*')) for obj_id
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

    def __str__(self):
        if len(self.assumptions) == 0:
            assumptions_str = ""
        else:
            assumptions_str = " assuming {" + ", ".join(
                str(assumption) for assumption in self.assumptions) + "}"
        if self.expr is not None:
            return "Unable to prove " + \
                str(self.expr) + assumptions_str + ":\n" + self.message
        else:
            return "Proof step failed" + assumptions_str + ":\n" + self.message


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


class CircularLogic(ProofFailure):
    def __init__(self, proving_theorem, presumed_theorem):
        ProofFailure.__init__(
            self,
            presumed_theorem.proven_truth.expr,
            [],
            "Circular Logic")
        self.proving_theorem = proving_theorem
        self.presumed_theorem = presumed_theorem

    def __str__(self):
        return str(self.presumed_theorem) + ' cannot be presumed while proving ' + \
            str(self.proving_theorem) + ' due to a circular dependence'


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
