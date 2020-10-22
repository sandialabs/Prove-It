"""
A Proof is a directed, acyclic graph (DAG) that represents the Prove-It
proof for a KnownTruth.  Each object represents a derivation step
(Assumption, ModusPonens, HypotheticalReasoning, Specialization,
or Generalization) and has references to other KnownTruths that
are directly required, each with its Proof.  In this way, the
Proof objects form a DAG.
"""

from collections import OrderedDict
import re
from proveit._core_.known_truth import KnownTruth
from proveit._core_._unique_data import meaningData, styleData
from .defaults import defaults
from .context import Context

class Proof:

    # Map each Proof to the first instantiation of it that was created (noting that
    # multiple Proof objects can represent the same Proof and will have the same hash value).
    # Using this, internal references (between KnownTruths and Proofs) unique .
    uniqueProofs = dict()

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information in
        the Proof jurisdiction.
        '''
        Proof.uniqueProofs.clear()
        Assumption.allAssumptions.clear()
        Theorem.allTheorems.clear()
        _ShowProof.show_proof_by_id.clear()

    def __init__(self, provenTruth, requiredTruths,
                 markedRequiredTruthIndices=None):

        '''
        # Uncomment to print useful debugging information when tracking side-effects.
        if not isinstance(self, Theorem) and not isinstance(self, Axiom):
            print "prove", provenTruth.expr
        '''

        assert isinstance(provenTruth, KnownTruth)
        for requiredTruth in requiredTruths:
            assert isinstance(requiredTruth, KnownTruth)
        # note: the contained KnownTruth and Proofs are subject to style changes on a Proof instance basis.
        self.provenTruth = provenTruth
        self.requiredTruths = tuple(requiredTruths)
        if markedRequiredTruthIndices is None:
            self.markedRequiredTruthIndices = set()
        else:
            self.markedRequiredTruthIndices = \
                set(markedRequiredTruthIndices)
        for idx in self.markedRequiredTruthIndices:
            if not isinstance(idx, int) or idx < 0 or idx > len(requiredTruths):
                raise ValueError("markedRequiredTruthIndices must be a set "
                                 "of integers indexing requiredTruths")

        # The meaning data is shared among Proofs with the same structure disregarding style
        self._meaningData = meaningData(self._generate_unique_rep(lambda obj : hex(obj._meaning_id)))
        if not hasattr(self._meaningData, 'requiredProofs'):
            self._meaningData.requiredProofs = [requiredTruth.proof() for requiredTruth in requiredTruths]
            self._meaningData._dependents = set() # meanng data of proofs that directly require this one

            # Is this a usable Proof?  An unusable proof occurs when trying to prove a Theorem
            # that must explicitly presume Theorems that are not fully known in order to
            # avoid circular logic.  They can also be manually introduced via Proof.disable().
            self._meaningData._unusableProof = None # When unusable, this will point to the unusable theorem
                                           # being applied directly or indirectly.

        # The style data is shared among Proofs with the same structure and style.
        self._styleData = styleData(self._generate_unique_rep(lambda obj : hex(obj._style_id)))

        # reference this unchanging data of the unique 'meaning' data
        self._meaning_id = self._meaningData._unique_id

        # reference this data of the unique 'meaning' data, but note that these
        # are subject to change (as proofs are disabled and as new dependencies are added).
        self.requiredProofs = self._meaningData.requiredProofs
        self._dependents = self._meaningData._dependents

        all_required_proofs = self.allRequiredProofs()
        all_required_truths = {required_proof.provenTruth for required_proof in all_required_proofs if required_proof is not self}
        original_proof = self.provenTruth not in all_required_truths

        if original_proof:
            # As long as this is not a useless self-dependent proof (a proof that depends upon
            # a different proof of the same truth which should never actually get used),
            # track the dependencies of required proofs so they can be updated appropriated if there are
            # changes due to proof disabling.
            for requiredProof in self.requiredProofs:
                requiredProof._dependents.add(self)

        if not hasattr(self._meaningData, 'numSteps'):
            # determine the number of unique steps required for this proof
            self._meaningData.numSteps = len(all_required_proofs)

        # establish some parent-child relationships (important in case styles are updated)
        self._styleData.addChild(self, self.provenTruth)
        for requiredTruth in self.requiredTruths:
            self._styleData.addChild(self, requiredTruth)

        self._style_id = self._styleData._unique_id

        if not original_proof:
            self._meaningData._unusableProof = self # not usable because it is not useful
            assert provenTruth.proof() is not None, "There should have been an 'original' proof"
            return

        requiringUnusableProof = False
        for requiredProof in self.requiredProofs:
            if not requiredProof.isUsable():
                # Mark proofs as unusable when using an "unusable" theorem
                # directly or indirectly.  Theorems are marked as unusable
                # when a proof for some Theorem is being generated as a
                # means to avoid circular logic.
                self._meaningData._unusableProof = requiredProof._meaningData._unusableProof
                # Raise an UnusableProof expection below (after calling _recordBestProof
                # to indicate the proof is unusable).
                requiringUnusableProof = True
                break # it only take one

        # if it is a Theorem, set its "usability", avoiding circular logic
        if self.isUsable():
            self._setUsability()
        # this new proof may be the first proof, make an old one obselete, or be born obsolete itself.
        #hadPreviousProof = (provenTruth.proof() is not None and provenTruth.isUsable())
        provenTruth._addProof(self)
        if requiringUnusableProof:
            # Raise an UnusableProof exception when an attempt is made
            # to use an "unusable" theorem directly or indirectly.
            raise UnusableProof(KnownTruth.theoremBeingProven, self._meaningData._unusableProof)
        if provenTruth.proof()==self and self.isUsable(): # don't bother with side effects if this proof was born obsolete or unusable
            # May derive any side-effects that are obvious consequences arising from this truth
            # (if it has not already been processed):
            provenTruth.deriveSideEffects(defaults.assumptions)

    def _updateDependencies(self, newproof):
        '''
        Swap out this oldproof for the newproof in all dependents and update their numSteps
        and usability status.
        '''
        oldproof = self
        for dependent in oldproof._dependents:
            revised_dependent = False
            i = 0
            try:
                while True:
                    i = dependent.requiredProofs.index(oldproof, i)
                    dependent.requiredProofs[i] = newproof
                    revised_dependent = True
            except ValueError:
                pass
            assert revised_dependent, "Incorrect dependency relationship"
            newproof._dependents.add(dependent)
            if all(required_proof.isUsable() for required_proof in dependent.requiredProofs):
                dependent._meaningData._unusableProof = None # it is usable again
                dependent._meaningData.numSteps = len(dependent.allRequiredProofs())
                dependent.provenTruth._addProof(dependent) # add it back as an option

    def _setUsability(self):
        pass # overloaded for the Theorem type Proof

    def _generate_unique_rep(self, objectRepFn):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        # Internally, for self._meaning_rep and self._style_rep, we will use self.requiredTruths in the unique representation
        # and the proofs are subject to change (if anything is disabled).
        # For external storage (see _context_storage.py), we will use self.requiredProofs, locking the mapping from KnonwTruths of self.requiredTruths to Proofs.
        required_objs = (self.requiredProofs
                         if hasattr(self, 'requiredProofs')
                         else self.requiredTruths)
        required_obj_marks = [('*' if k in self.markedRequiredTruthIndices
                             else '') for k in range(len(required_objs))]
        required_objs_str = ','.join(objectRepFn(obj)+mark for obj, mark
                                     in zip(required_objs, required_obj_marks))
        return (self._generate_step_info(objectRepFn) +
                '[%s];[%s]'
                %(objectRepFn(self.provenTruth), required_objs_str))

    def _generate_step_info(self, objectRepFn):
        '''
        Generate information about this proof step.
        Overridden by Specialization which also needs to including the mapping information
        and uses the given function to obtain representations of sub-Object.
        '''
        return self.stepType() + ':'

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
        objIds = re.split("\{|\[|,|:|;|\]|\}",remaining)
        # Remove the '*' marks, marking the "equality replacement
        # requirements".
        return [objId.rstrip('*') for objId in objIds if len(objId) > 0]

    @staticmethod
    def _showProof(context, proof_id, unique_rep):
        '''
        Given a unique representation string, returns a _ShowProof
        object that mocks up a stored proof for the purposes of
        displaying it.
        '''
        # Skip the step type (and axiom/theorem name if it is either of
        # those types) which is in the beginning and followed by a ':'
        if unique_rep[:6] != 'Proof:':
            raise ValueError("Invalid 'unique_rep' for Proof: %s"%unique_rep)
        step_info, remaining = unique_rep[6:].split(':', 1)
        # extract groups each wrapped in braces, either '{..}' or '[..]'
        group_strs = []
        while len(remaining) > 0:
            if remaining[0]==';':
                remaining=remaining[1:]
            start_brace = remaining[0]
            if start_brace not in ('{', '['):
                raise ValueError("Invalid starting brace of 'unique_rep': %s"%remaining[0])
            end_brace = '}' if start_brace=='{' else ']'
            remaining=remaining[1:]
            group_str, remaining = remaining.split(end_brace, 1)
            group_strs.append(group_str)
        # The id's of each group come between the punctuation:
        # ';', ':', ','.
        groups = []
        for group_str in group_strs:
            objIds = re.split(",|:|;",group_str)
            groups.append([objId for objId in objIds if len(objId) > 0])
        if proof_id in _ShowProof.show_proof_by_id:
            return _ShowProof.show_proof_by_id[proof_id]
        return _ShowProof(context, proof_id, step_info, groups)

    def isUsable(self):
        '''
        Returns True iff this Proof is usable.  A Proof may be unusable
        because it was manually disabled or because it is not being presumed
        while trying to prove a Theorem (other Theorems must be explicitly
        presumed in order to avoid circular logic).
        '''
        return self._meaningData._unusableProof is None

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
                if dependent_proof.provenTruth.proof() == dependent_proof:
                    # include the sub-dependents iff this dependent is actually in use
                    to_process.extend(dependent_proof._dependents)

        # Disable all dependents
        for dependent_proof in all_dependents:
            dependent_proof._meaningData._unusableProof = self
            dependent_proof.provenTruth._discardProof(dependent_proof)

        # Check if alternate usable proofs are available for the proofs that we disabled.
        # Make multiple passes to ensure new possibilities and best options fully propagate.
        continue_revisions = True
        while continue_revisions:
            continue_revisions = False
            for dependent_proof in all_dependents:
                if dependent_proof.provenTruth.proof() == dependent_proof:
                    # Check for an alternate to this disabled dependent proof.
                    if dependent_proof.provenTruth._reviseProof():
                        continue_revisions = True

    def __eq__(self, other):
        if isinstance(other, Proof):
            return self._meaning_id == other._meaning_id
        else: return False # other must be an Expression to be equal to self

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._meaning_id

    def numSteps(self):
        '''
        Return the number of unique steps in the proof.
        '''
        return self._meaningData.numSteps

    def usedAxioms(self):
        '''
        Returns the set of names of axioms that are used directly (not via other theorems) in this proof.
        '''
        return set().union(*[requiredProof.usedAxioms() for requiredProof in self.requiredProofs])

    def usedTheorems(self):
        '''
        Returns the set of names of axioms that are used directly (not via other theorems) in this proof.
        '''
        return set().union(*[requiredProof.usedTheorems() for requiredProof in self.requiredProofs])

    def assumptions(self):
        return self.provenTruth.assumptions

    def getLink(self):
        '''
        Return the link to the proof notebook.  It the Proof is a
        Theorem or Axiom, this is overridden to return the link to
        the theorem/axiom definition.
        '''
        context = Context()
        return context.proofNotebook(self)

    def __setattr__(self, attr, value):
        '''
        Proofs should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).  Also,
        _dependents is an exception which can be updated internally.
        '''
        if hasattr(self, attr):
            raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value

    def enumeratedProofSteps(self):
        '''
        Returns a list of Proof objects that includes self and
        all of its direct and indirect requirements.  Duplicates
        will not be included, but they will be presented in an
        order which makes it clear that the dependencies are
        acyclic by making sure requirements come after dependents.
        '''
        from ._dependency_graph import orderedDependencyNodes
        return orderedDependencyNodes(self, lambda proof : proof.requiredProofs)

    def allRequiredProofs(self):
        '''
        Returns the set of directly or indirectly required proofs.
        '''
        subProofSets = [requiredProof.allRequiredProofs() for requiredProof in self.requiredProofs]
        return set([self]).union(*subProofSets)

    def _repr_html_(self):
        if not defaults.display_latex:
            return None # No LaTeX display at this time.
        proofSteps = self.enumeratedProofSteps()
        html = '<table><tr><th>&nbsp;</th><th>step type</th><th>requirements</th><th>statement</th></tr>\n'
        first_requirements = None
        # If this is a _ShowProof object, _style_id will be a str.
        proof_id = self._style_id if isinstance(self._style_id, str) \
                    else hex(self._style_id)

        # For convenience, we will reference all of the first (top-level)
        # requirements at the top even if it is a simple reference.
        amendedProofSteps = []
        for k, proof in enumerate(proofSteps):
            if k == 0:
                first_requirements = iter(proof.requiredProofs)
            else:
                while first_requirements is not None:
                    try:
                        req = next(first_requirements)
                        if req == proof:
                            break
                        # Just reference a later step.
                        amendedProofSteps.append(_ProofReference(req))
                    except StopIteration:
                        # Done with the first requirements:
                        first_requirements = None
            amendedProofSteps.append(proof)
        proofSteps = amendedProofSteps

        any_marked = False
        def req_link(proof, req_idx, n):
            nonlocal any_marked
            is_marked = (req_idx in proof.markedRequiredTruthIndices)
            if is_marked: any_marked=True
            mark_str = r'<sup>*</sup>' if is_marked else ''
            return ('<a href="#%s_step%d">%d</a>%s'
                    %(proof_id, n, n, mark_str))
        proofNumMap = {proof:k for k, proof in enumerate(proofSteps)}
        for k, proof in enumerate(proofSteps):
            html += '<tr><td><a name="%s_step%d">%d</a></td>'%(proof_id,k,k)
            if k==0:
                # The first (top-level) proof has requirements at the
                # top by design (though some of these may be references to
                # later steps).
                requiredProofNums = \
                    ', '.join(req_link(proof, k, k+1) for k, _
                              in enumerate(proof.requiredProofs))
            else:
                requiredProofNums = \
                    ', '.join(req_link(proof, k, proofNumMap[requiredProof])
                              for k, requiredProof
                              in enumerate(proof.requiredProofs))
            html += '<td>%s</td><td>%s</td>'%(proof.stepType(), requiredProofNums)
            html += '<td>%s</td>'%proof.provenTruth._repr_html_()
            html += '</tr>\n'
            if proof.stepType()=='instantiation':
                html += '<tr><td>&nbsp;</td><td colspan=4 style="text-align:left">' + proof._mapping('HTML') + '</td></tr>'
            if proof.stepType() in {'axiom', 'theorem', 'conjecture'}:
                html += '<tr><td>&nbsp;</td><td colspan=4 style-"text-align:left">'
                html += '<a class="ProveItLink" href="%s">'%proof.getLink() + str(proof.context) + '.' + proof.name + '</a>'
                html += '</td></tr>'
        if any_marked:
            html += ('<tr><td colspan=4 style="text-align:left">'
                     r'<sup>*</sup>equality replacement requirements'
                     '</td></tr>')
        html += '</table>'
        return html

    def __repr__(self):
        proofSteps = self.enumeratedProofSteps()
        proofNumMap = {proof:k for k, proof in enumerate(proofSteps)}
        any_marked = False
        def req_ref(proof, req_idx):
            global any_marked
            req = proof.requiredProofs[req_idx]
            is_marked = (req_idx in proof.markedRequiredTruthIndices)
            if is_marked: any_marked=True
            mark_str = r'*' if is_marked else ''
            return ('%d%s'%(proofNumMap[req], mark_str))
        out_str = '\tstep type\trequirements\tstatement\n'
        for k, proof in enumerate(proofSteps):
            out_str += str(k) + '\t'
            required_proof_refs = \
                ', '.join(req_ref(proof, k) for k
                          in range(len(proof.requiredProofs)))
            out_str += proof.stepType() + '\t' + required_proof_refs + '\t'
            out_str += proof.provenTruth.string(performUsabilityCheck=False)
            out_str += '\n'
            if proof.stepType()=='instantiation':
                out_str += '\t' + proof._mapping('str') + '\n'
            if proof.stepType()=='axiom' or proof.stepType()=='theorem':
                out_str += '\t' + str(proof.context) + '.' + proof.name + '\n'
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
        self.requiredProofs = [ref]
        self.provenTruth = ref.provenTruth
        self.markedRequiredTruthIndices = set() # nothing marked

    def stepType(self):
        # only used in the HTML version
        return '<i>reference</i>'

class Assumption(Proof):
    # Map expressions to corresponding assumption objects.
    allAssumptions = dict()

    def __init__(self, expr, assumptions=None):
        from proveit import ExprRange
        assert expr not in Assumption.allAssumptions, \
            ("Do not create an Assumption object directly; "
             "use Assumption.makeAssumption instead.")
        assumptions = defaults.checkedAssumptions(assumptions)
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
            Proof.__init__(self, KnownTruth(assumed_truth, {expr}), [])
        finally:
            # Restore the original default assumptions
            defaults.assumptions = prev_default_assumptions
        Assumption.allAssumptions[expr] = self

    @staticmethod
    def makeAssumption(expr, assumptions):
        '''
        Return an Assumption object, only creating it if it doesn't
        already exist.  assumptions must already be 'checked' and in
        tuple form.
        '''
        if expr in Assumption.allAssumptions:
            preexisting = Assumption.allAssumptions[expr]
            # The Assumption object exists already, but it's
            # side-effects may not have been derived yet under the
            # given assumptions.
            # This can happen when automation is temporarily disabled or
            # when assumptions change.
            preexisting.provenTruth.deriveSideEffects(assumptions)
            return preexisting
        return Assumption(expr, assumptions)

    def stepType(self):
        return 'assumption'

class Axiom(Proof):
    def __init__(self, expr, context, name):
        if not isinstance(context, Context):
            raise ValueError("An axiom 'context' must be a Context object")
        if not isinstance(name, str):
            raise ValueError("An axiom 'name' must be a string")
        self.context = context
        self.name = name
        Proof.__init__(self, KnownTruth(expr, frozenset()), [])

    def _generate_step_info(self, objectRepFn):
        return self.stepType() + '_' + str(self) + ':'

    def stepType(self):
        return 'axiom'

    def _storedAxiom(self):
        from ._context_storage import StoredAxiom
        return StoredAxiom(self.context, self.name)

    def getLink(self):
        '''
        Return the HTML link to the axiom definition.
        '''
        return self._storedAxiom().getDefLink()

    def usedAxioms(self):
        return {self}

    def directDependents(self):
        '''
        Returns the theorems that depend directly upon this axioms.
        '''
        return self._storedAxiom().readDependentTheorems()

    def allDependents(self):
        return self._storedAxiom().allDependents()

    def __str__(self):
        return self.context.name + '.' + self.name

class Theorem(Proof):
    allTheorems = []

    def __init__(self, expr, context, name):
        if not isinstance(context, Context):
            raise ValueError("A theorem 'package' must be a Context object")
        if not isinstance(name, str):
            raise ValueError("A theorem 'name' must be a string")
        self.context = context
        self.name = name
        # keep track of proofs that may be used to prove the theorem
        # before 'beginProof' is called so we will have the proof handy.
        self._possibleProofs = []
        # Note that _setUsability will be called within Proof.__init__
        Proof.__init__(self, KnownTruth(expr, frozenset()), [])
        Theorem.allTheorems.append(self)

    def _generate_step_info(self, objectRepFn):
        return self.stepType() + '_' + str(self) + ':'

    def stepType(self):
        if self.isConjecture():
            return 'conjecture'
        return 'theorem'

    def usedTheorems(self):
        return {self}

    def __str__(self):
        return self.context.name + '.' + self.name

    def __repr__(self):
        return self.context.name + '.' + self.name

    def containingPrefixes(self):
        '''
        Yields all containing context names and the full theorem name.
        '''
        s = str(self)
        hierarchy = s.split('.')
        for k in range(1, len(hierarchy)):
            yield '.'.join(hierarchy[:k])
        yield s

    @staticmethod
    def updateUsability():
        for theorem in Theorem.allTheorems:
            theorem._setUsability()

    def _storedTheorem(self):
        from ._context_storage import StoredTheorem
        return StoredTheorem(self.context, self.name)

    def getLink(self):
        '''
        Return the HTML link to the theorem proof file.
        '''
        return self._storedTheorem().getProofLink()

    def recordPresumedContexts(self, presumed_context_names):
        '''
        Record information about what other contexts are
        presumed in the proof of this theorem.
        '''
        self._storedTheorem().recordPresumedContexts(presumed_context_names)

    def presumedContexts(self):
        '''
        Return the list of presumed contexts.
        '''
        return self._storedTheorem().presumedContexts()

    def recordPresumedTheorems(self, explicitly_presumed_theorem_names):
        '''
        Record information about what othere theorems are
        presumed in the proof of this theorem.
        '''
        self._storedTheorem().recordPresumedTheorems(explicitly_presumed_theorem_names)

    def explicitlyPresumedTheoremNames(self):
        '''
        Return the list of names of explicitly presumed theorems.
        (indicated after 'presuming' in the proof notebook).
        '''
        return self._storedTheorem().explicitlyPresumedTheoremNames()

    def getAllPresumedTheoremNames(self):
        '''
        Return the set of full names of presumed theorems that are
        directly or indirectly presumed by the theorem of the given name
        in this context.
        '''
        return self._storedTheorem().getAllPresumedTheoremNames()

    def recordProof(self, proof):
        '''
        Record the given proof as the proof of this theorem.  Updates
        dependency links (usedAxioms.txt, usedTheorems.txt, and usedBy.txt files)
        and proven dependency indicators (various provenTheorems.txt files
        for theorems that depend upon the one being proven) appropriately.
        '''
        self._storedTheorem().recordProof(proof)

    def removeProof(self):
        '''
        Remove the proof for the given theorem and all obsolete dependency
        links.
        '''
        self._storedTheorem().removeProof()

    def hasProof(self):
        '''
        Returns true if and only if this theorem has a recorded proof.
        '''
        return self._storedTheorem().hasProof()

    def isFullyProven(self):
        '''
        Returns true if and only if this theorem is fully proven
        (it has a recorded proof and all dependent theorems are fully
        proven, all the way to axioms which don't require proofs).
        '''
        return self._storedTheorem().isComplete()
    
    def isConjecture(self):
        '''
        A "Theorem" that is not fully proven is a "conjecture".
        '''
        return not self.isFullyProven()

    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or indirectly)
        by the theorem.  Also, if the given theorem is not completely proven,
        return the set of unproven theorems that are required (directly or
        indirectly).  Returns this axiom set and theorem set as a tuple.
        '''
        return self._storedTheorem().allRequirements()

    def allUsedTheoremNames(self):
        '''
        Returns the set of theorems used to prove the given theorem, directly
        or indirectly.
        '''
        return self._storedTheorem().allUsedTheoremNames()

    def directDependents(self):
        '''
        Returns the theorems that depend directly upon this axioms.
        '''
        return self._storedTheorem().readDependentTheorems()

    def allDependents(self):
        '''
        Returns the set of theorems that are known to depend upon this
        theorem directly or indirectly.
        '''
        return self._storedTheorem().allDependents()

    def _setUsability(self):
        '''
        Sets the '_unusableProof' attribute to disable the
        theorem if some theorem is being proven and this
        theorem is not presumed or is an alternate proof for the
        same theorem.  Also, if it is presumed, ensure the logic
        is not circular.  Generally, this is preventing circular
        logic.  This applies when a proof has begun
        (see KnownTruth.beginProof in known_truth.py).
        When KnownTruth.theoremBeingProven is None, all Theorems are allowed.
        Otherwise only Theorems named in the KnownTruth.presumingTheoremNames set
        or contained within any of the KnownTruth.presumingPrefixes
        (i.e., context) are allowed.
        '''
        #from proveit.certify import isFullyProven
        if KnownTruth.theoremBeingProven is None:
            self._meaningData._unusableProof = None # Nothing being proven, so all Theorems are usable
            return
        legitimately_presumed = False
        stored_theorem = self._storedTheorem()
        theorem_being_proven_str = str(KnownTruth.theoremBeingProven)
        if self.provenTruth==KnownTruth.theoremBeingProven.provenTruth:
            # Note that two differently-named theorems for the same thing may exists in
            # order to show an alternate proof.  In that case, we want to disable
            # the other alternates as well so we will be sure to generate the new proof.
            self.disable()
            return
        else:
            presumed_via_context = not KnownTruth.presumingPrefixes.isdisjoint(self.containingPrefixes())
            if str(self) in KnownTruth.presumingTheoremNames or presumed_via_context:
                # This Theorem is being presumed specifically, or a context in which it is contained is presumed.
                # Presumption via context (a.k.a. prefix) is contingent upon not having a mutual presumption
                # (that is, some theorem T can presume everything in another context except for theorems
                # that presume T or, if proven, depend upon T).
                # When Theorem-specific presumptions are mutual, a CircularLogic error is raised when either
                # is being proven.
                # check the "presuming information, recursively, for circular logic.
                presumed_theorem_names = stored_theorem.getAllPresumedTheoremNames()
                # If this theorem has a proof, include all dependent theorems as
                # presumed (this may have been presumed via context, so this can contain
                # more information than the specifically presumed theorems).
                if stored_theorem.hasProof():
                    presumed_theorem_names.update(stored_theorem.allUsedTheoremNames())
                if presumed_via_context:
                    if theorem_being_proven_str not in presumed_theorem_names:
                        # Presumed via context without any mutual specific presumption or existing co-dependence.
                        legitimately_presumed=True # It's legit; don't disable.
                    # If there is a conflict, don't presume something via context.
                else:
                    # This Theorem is being presumed specifically
                    if (theorem_being_proven_str in presumed_theorem_names):
                        # Theorem-specific presumptions are mutual.  Raise a CircularLogic error.
                        raise CircularLogic(KnownTruth.theoremBeingProven, self)
                    legitimately_presumed=True # This theorem is specifically and legitimately being presumed.
        if not legitimately_presumed:
            # This Theorem is not usable during the proof (if it is needed, it must be
            # presumed or fully proven).  Propagate this fact to all dependents.
            self.disable()

def _checkImplication(implicationExpr, antecedentExpr, consequentExpr):
    '''
    Make sure the implicationExpr is a proper implication with
    antecedentExpr as the antecedent and consequentExpr as the consequent.
    '''
    from proveit.logic import Implies
    assert isinstance(implicationExpr, Implies),  'The result of hypothetical reasoning must be an Implies operation'
    assert len(implicationExpr.operands)==2, 'Implications are expected to have two operands'
    assert antecedentExpr==implicationExpr.operands[0], 'The result of hypothetical reasoning must be an Implies operation with the proper antecedent'
    assert consequentExpr==implicationExpr.operands[1], 'The result of hypothetical reasoning must be an Implies operation with the proper consequent'

class ModusPonens(Proof):
    def __init__(self, implicationExpr, assumptions=None):
        from proveit.logic import Implies
        assumptions = defaults.checkedAssumptions(assumptions)
        prev_default_assumptions = defaults.assumptions
        defaults.assumptions = assumptions # these assumptions will be used for deriving any side-effects
        try:
            # obtain the implication and antecedent KnownTruths
            assert isinstance(implicationExpr, Implies) and len(implicationExpr.operands)==2, 'The implication of a modus ponens proof must refer to an Implies expression with two operands'
            try:
                # Must prove the implication under the given assumptions.
                implicationTruth = implicationExpr.prove(assumptions)
            except ProofFailure:
                raise ModusPonensFailure(implicationExpr.operands[1], assumptions, 'Implication, %s, is not proven'%str(implicationExpr))
            try:
                # Must prove the antecedent under the given assumptions.
                antecedentTruth = implicationExpr.operands[0].prove(assumptions)
            except ProofFailure:
                raise ModusPonensFailure(implicationExpr.operands[1], assumptions, 'Antecedent of %s is not proven'%str(implicationExpr))
            # remove any unnecessary assumptions (but keep the order that was provided)
            assumptionsSet = implicationTruth.assumptionsSet | antecedentTruth.assumptionsSet
            assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
            # we have what we need; set up the ModusPonens Proof
            consequentTruth = KnownTruth(implicationExpr.operands[1], assumptions)
            _checkImplication(implicationTruth.expr, antecedentTruth.expr, consequentTruth.expr)
            self.implicationTruth = implicationTruth
            self.antecedentTruth = antecedentTruth
            Proof.__init__(self, consequentTruth, [self.implicationTruth, self.antecedentTruth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def stepType(self):
        return 'modus ponens'

class Deduction(Proof):
    def __init__(self, consequentTruth, antecedentExpr):
        from proveit import ExprRange
        from proveit.logic import Implies, And
        if isinstance(antecedentExpr, ExprRange):
            # Assumption ranges must be transformed to a
            # conjunction form on the other side.
            elim_assumption = antecedentExpr
            antecedentExpr = And(antecedentExpr)
        else:
            elim_assumption = antecedentExpr
        assumptions = [assumption for assumption in consequentTruth.assumptions
                       if assumption != elim_assumption]
        prev_default_assumptions = defaults.assumptions
         # These assumptions will be used for deriving any side-effects
        defaults.assumptions = assumptions
        try:
            implicationExpr = Implies(antecedentExpr, consequentTruth.expr)
            implicationTruth = KnownTruth(implicationExpr, assumptions)
            self.consequentTruth = consequentTruth
            Proof.__init__(self, implicationTruth, [self.consequentTruth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def stepType(self):
        return 'deduction'

class Instantiation(Proof):
    def __init__(self, orig_known_truth, num_forall_eliminations,
                 repl_map, equiv_alt_expansions, assumptions):
        '''
        Create the specialization+instantiation proof step that eliminates
        some number of nested Forall operations (specialization) and
        simultaneously replaces Variables with Expressions (instantiation)
        according to the replacement map (repl_map). A Variable that is
        a parameter variable of an internal Lambda expression may only
        be relabeled; it will not be replaced with a non-Variable expression
        within the scop of the Lambda expression.

        See Expression.substituted for details regarding the replacement rules.
        '''
        from proveit import (Expression, Lambda, ExprRange, ExprTuple,
                             IndexedVar)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (getParamVar, LambdaApplicationError)

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
                                %(repl, repl.__class__))
            if isinstance(key, ExprTuple):
                # If the key is an ExprTuple, it must either be a
                # range (or range of ranges, etc.) of an indexed variable 
                # for a full expansion, or it is an "equivalent alternative
                # expansion".
                # Should already have been checked in
                # KnownTruth.instantiate:
                try:
                    for param_entry in key:
                        getParamVar(param_entry)
                except TypeError as e:
                    assert False, ("Should have been checked in 'instantiate' "
                                   "method:\n%s"%str(e))
                parameters.append(key[0])
            else:
                parameters.append(key)
        prev_default_assumptions = set(defaults.assumptions)
        try:
            # These assumptions will be used for deriving any
            # side-effects:
            defaults.assumptions = set(assumptions)
            if not isinstance(orig_known_truth, KnownTruth):
                raise TypeError("May only 'instantiate' a KnownTruth")
            if orig_known_truth.proof() is None:
                raise UnusableProof(KnownTruth.theoremBeingProven,
                                    orig_known_truth)

            # The "original" KnownTruth is the first "requirement truth" for
            # this derivation step.
            orig_subbed_assumptions = []
            requirements = []
            equality_repl_requirements = set()

            # Make possible substitutions in the "original" KnownTruth
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
            for assumption in orig_known_truth.assumptions:
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
            # original_known_truth plus the assumptions that were
            # provided.
            assumptions = tuple(orig_subbed_assumptions) + assumptions
            # Eliminate duplicates.
            assumptions = tuple(OrderedDict.fromkeys(assumptions))
            # Make this the new default (for side-effects).
            defaults.assumptions = assumptions

            instantiated_expr = \
                Instantiation._instantiated_expr(
                        orig_known_truth, num_forall_eliminations,
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
            # in the original KnownTruth.
            def get_key_var(key):
                if isinstance(key, ExprTuple):
                    assert len(key)>=1
                    return getParamVar(key[0])
                return getParamVar(key)
            repl_var_keys = {get_key_var(key):key for key in repl_map.keys()}
            repl_vars = repl_var_keys.keys()
            repl_vars = list(orig_known_truth.orderOfAppearance(repl_vars))
            # And remove duplicates.
            repl_vars = list(OrderedDict.fromkeys(repl_vars))

            # Map variables to sets of tuples that represent the
            # same range of indexing for equivalent alternative
            # expansions.  For example,
            #   {x_1, ..., x_{n+1}, x_1, ..., x_n, x_{n+1}}.
            var_range_forms = dict()
            for var_range_form, expansion in equiv_alt_expansions.items():
                var = getParamVar(var_range_form[0])
                var_range_forms.setdefault(var, set()).add(var_range_form)

            # We have what we need; set up the Instantiation Proof
            self.orig_known_truth = orig_known_truth
            # Exclude anything in the repl_map that does not appear in
            # the original KnownTruth:
            mapping = dict()
            mapping_var_order = []
            def var_range_form_sort(var_tuple):
                # For sorting equivalent ExprTuples of indexed
                # variables (e.g., {(x_1, ..., x_{n+1}),
                #                   (x_1, ..., x_n, x_{n+1})})
                # put ones with the fewest number of entries first
                # but break ties arbitrarily via the "meaning id".
                return (len(var_tuple), var_tuple._meaning_id)
            for var in repl_vars:
                if var in repl_map:
                    # The variable itself is in the replacement map.
                    mapping[var] = repl_map[var]
                    mapping_var_order.append(var)
                if var in var_range_forms:
                    # There are replacements for various forms of the
                    # variable indexed over the same range.
                    # We'll sort these in an order going
                    # from the fewest # of entries to the most.
                    for var_range_form in sorted(var_range_forms[var],
                                                 key=var_range_form_sort):
                        mapping[var_range_form] = \
                            equiv_alt_expansions[var_range_form]
                        mapping_var_order.append(var_range_form)
            self.mapping_var_order = mapping_var_order
            self.mapping = mapping
            instantiated_truth = KnownTruth(instantiated_expr, assumptions)
            # Make the 'original known truth' be the 1st requirement.
            requirements.insert(0, orig_known_truth)
            # Mark the requirements that are "equality replacements".
            marked_req_indices = set()
            for k, req in enumerate(requirements):
                if req in equality_repl_requirements:
                    marked_req_indices.add(k)
            Proof.__init__(self, instantiated_truth, requirements,
                           marked_req_indices)
        except LambdaApplicationError as e:
            raise InstantiationFailure(orig_known_truth, repl_map,
                                       assumptions, str(e))
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def _generate_step_info(self, objectRepFn):
        '''
        Generate information about this proof step, including mapping
        information for this specialization.
        '''
        mapping = self.mapping
        mapping_info = ','.join(objectRepFn(var) + ':' + objectRepFn(mapping[var])
                               for var in self.mapping_var_order)
        return self.stepType() + ':{' + mapping_info + '}'

    def stepType(self):
        return 'instantiation'

    def _single_mapping(self, var, replacement, formatType):
        from proveit import Function, Lambda
        formatted = lambda expr : expr._repr_html_() if formatType=='HTML' else str(expr)
        if isinstance(replacement, Lambda):
            return (formatted(Function(var, replacement.parameter_or_parameters))
                    + ' : ' + formatted(replacement.body))
        return formatted(var) + ' : ' + formatted(replacement)

    def _mapping(self, formatType='HTML'):
        if formatType=='HTML':
            out = '<span style="font-size:20px;">'
        else: out = ''
        out += ', '.join(self._single_mapping(var, self.mapping[var], formatType)
                         for var in self.mapping_var_order)
        if formatType=='HTML':
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
                        %(orig_expr, num_nested_foralls))
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
    def _instantiated_expr(original_known_truth, num_forall_eliminations,
                           instantiation_params, repl_map,
                           equiv_alt_expansions,
                           assumptions, requirements,
                           equality_repl_requirements):
        '''
        Return the instantiated version of the right side of the
        original_known_truth.  The assumptions on the left side of
        the turnstile are treated in Instantiation.__init__.

        Eliminates the specified number of Forall operations,
        substituting all  of the corresponding instance variables
        according to repl_map.
        '''
        from proveit import (Lambda, Conditional, ExprTuple, ExprRange)
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            getParamVar
        from proveit.logic import Forall, And

        # Eliminate the desired number of Forall operations and extract
        # appropriately mapped conditions.
        expr = original_known_truth.expr
        def raiseFailure(msg):
            raise InstantiationFailure(original_known_truth, repl_map,
                                       assumptions, msg)
        instantiation_param_vars = [getParamVar(param) for param
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
                if param_var==exclusion:
                    continue # skip the 'exclusion'
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
            if len(params)==0:
                return expr
            return Lambda._apply(
                    params, expr, *operands, allow_relabeling=True,
                    equiv_alt_expansions=equiv_alt_expansions,
                    assumptions=assumptions, requirements=requirements,
                    equality_repl_requirements=equality_repl_requirements)

        remaining_forall_eliminations = num_forall_eliminations
        while remaining_forall_eliminations>0:
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
                    param_var = getParamVar(param)
                    param_var_repl = repl_map.get(param_var, None)
                    if isinstance(param_var_repl, ExprTuple):
                        subbed_param = instantiate(param, exclusion=param_var)
                        if subbed_param not in repl_map:
                            subbed_param_tuple = ExprTuple(subbed_param)
                            if (subbed_param_tuple in repl_map and
                                    repl_map[subbed_param_tuple] !=
                                        param_var_repl):
                                raiseFailure("Inconsistent assignment of "
                                             "%s: %s, from instantiation of "
                                             "%s, versus %s."
                                             %(subbed_param_tuple,
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
                        raiseFailure('Unsatisfied condition: %s'
                                     %str(subbed_cond))

        # Make final instantiations in the inner instance expression.
        # Add to the lambda-application parameters anything that has
        # not yet been used
        return instantiate(expr)

class Generalization(Proof):
    def __init__(self, instanceTruth, newForallParamLists, newConditions=tuple()):
        '''
        A Generalization step wraps a KnownTruth (instanceTruth) in one or more Forall operations.
        The number of Forall operations introduced is the number of lists in newForallVarLists.
        The conditions are introduced in the order they are given at the outermost level that is
        applicable.  For example, if newForallParamLists is [[x, y], z]  and the new
        conditions are f(x, y) and g(y, z) and h(z), this will prove a statement of the form:
            forall_{x, y in Integers | f(x, y)} forall_{z | g(y, z), h(z)} ...
        '''
        from proveit import KnownTruth
        from proveit._core_.expression.lambda_expr.lambda_expr import \
            (getParamVar, _guaranteed_to_be_independent)
        from proveit.logic import Forall
        if not isinstance(instanceTruth, KnownTruth):
            raise GeneralizationFailure(None, [], 'May only generalize a KnownTruth instance')
        # the assumptions required for the generalization are the assumptions of
        # the original KnownTruth minus the all of the new conditions (including those
        # implied by the new domain).
        assumptions = set(instanceTruth.assumptions)
        prev_default_assumptions = defaults.assumptions
        defaults.assumptions = assumptions # these assumptions will be used for deriving any side-effects
        try:
            remainingConditions = list(newConditions)
            expr = instanceTruth.expr
            introducedForallVars = set()
            for k, newForallParams in enumerate(reversed(newForallParamLists)):
                newForallVars = [getParamVar(parameter)
                                 for parameter in newForallParams]
                introducedForallVars |= set(newForallVars)
                newConditions = []
                if k == len(newForallParamLists)-1:
                    # the final introduced Forall operation must use all of the remaining conditions
                    newConditions = remainingConditions
                else:
                    # use all applicable conditions in the supplied order
                    conditionApplicability = \
                        [not _guaranteed_to_be_independent(remaining_cond,
                                                           newForallVars)
                         for remaining_cond in remainingConditions]
                    newConditions = \
                        [remaining_cond for applicable, remaining_cond
                         in zip(conditionApplicability, remainingConditions)
                         if applicable]
                    remainingConditions = \
                        [remaining_cond for applicable, remaining_cond
                         in zip(conditionApplicability, remainingConditions)
                         if not applicable]
                # new conditions can eliminate corresponding assumptions
                assumptions -= set(newConditions)
                # create the new generalized expression
                generalizedExpr = Forall(
                        instanceParamOrParams=newForallParams,
                        instanceExpr=expr, conditions=newConditions)
                # make sure this is a proper generalization that doesn't break the logic:
                Generalization._checkGeneralization(generalizedExpr, expr)
                expr = generalizedExpr
            for assumption in assumptions:
                if not _guaranteed_to_be_independent(assumption, introducedForallVars):
                    raise GeneralizationFailure(generalizedExpr, assumptions, 'Cannot generalize using assumptions that involve any of the new forall variables (except as assumptions are eliminated via conditions or domains)')
            generalizedTruth = KnownTruth(generalizedExpr, assumptions)
            self.instanceTruth = instanceTruth
            self.newForallVars = newForallVars
            self.newConditions = newConditions
            Proof.__init__(self, generalizedTruth, [self.instanceTruth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def stepType(self):
        return 'generalizaton'

    @staticmethod
    def _checkGeneralization(generalizedExpr, instanceExpr):
        '''
        Make sure the generalizedExpr is a proper generalization of the
        instanceExpr.
        '''
        from proveit import Lambda, Conditional
        from proveit.logic import Forall
        assert isinstance(generalizedExpr, Forall), 'The result of a generalization must be a Forall operation'
        lambdaExpr = generalizedExpr.operand
        assert isinstance(lambdaExpr, Lambda), 'A Forall Expression must be in the proper form'
        expr = lambdaExpr.body
        while expr != instanceExpr:
            if isinstance(expr, Conditional):
                # Dig into the conditional.  Adding conditions only
                # weakens the statement, so it doesn't matter what
                # the conditions are.
                expr = expr.value
                if expr == instanceExpr: break
            if not isinstance(expr, Forall): break
            expr = expr.instanceExpr # take it another nested level if necessary
        assert expr == instanceExpr, 'Generalization not consistent with the original expression: ' + str(expr) + ' vs ' + str(instanceExpr)

class _ShowProof:
    '''
    A mocked-up quasi-Proof object just for the purposes of showing a
    stored proof.
    '''

    # Map proof_id's to _ShowProof objects that have been created.
    show_proof_by_id = dict()

    def __init__(self, context, proof_id, stepInfo, refObjIdGroups):
        self._style_id = proof_id
        if '_' in stepInfo:
            # Must be an axiom or theorem with the format
            # axiom_context.name or theorem_context.name
            self.step_type_str, full_name = stepInfo.split('_', 1)
            assert self.step_type_str in ('axiom', 'theorem', 'conjecture')
            full_name_segments = full_name.split('.')
            context_name = '.'.join(full_name_segments[:-1])
            self.context =  Context.getContext(context_name)
            self.name = full_name_segments[-1]
        else:
            self.context = context
            self.step_type_str = stepInfo
        if self.step_type_str=='instantiation':
            # Extract the mapping information.
            group = refObjIdGroups[0]
            var_mapping_pairs = [(context.getStoredExpr(group[i]),
                                  context.getStoredExpr(group[i+1])) \
                                 for i in range(0, len(group), 2)]
            self.mapping_var_order = [key for key, value in var_mapping_pairs]
            self.mapping = dict(var_mapping_pairs)
        self.provenTruth = context.getStoredKnownTruth(refObjIdGroups[-2][0])
        self.provenTruth._meaningData._proof = self
        self.requiredProofs = \
            [context.getShowProof(obj_id.rstrip('*')) for obj_id
             in refObjIdGroups[-1]]
        self.markedRequiredTruthIndices = \
            {k for k, obj_id in enumerate(refObjIdGroups[-1])
             if obj_id[-1]=='*'}
        _ShowProof.show_proof_by_id[proof_id] = self

    def _repr_html_(self):
        if not defaults.display_latex:
            return None # No LaTeX display at this time.
        return Proof._repr_html_(self)

    def stepType(self):
        return self.step_type_str

    def getLink(self):
        from ._context_storage import StoredAxiom, StoredTheorem
        if self.step_type_str=='axiom':
            return StoredAxiom(self.context, self.name).getDefLink()
        elif self.step_type_str in ('theorem', 'conjecture'):
            return StoredTheorem(self.context, self.name).getProofLink()
        else:
            return self.context.proofNotebook(self)

    def _single_mapping(self, *args):
        return Instantiation._single_mapping(self, *args)

    def _mapping(self, *args):
        return Instantiation._mapping(self, *args)

    def enumeratedProofSteps(self):
        return Proof.enumeratedProofSteps(self)

    def isUsable(self):
        return True

class ProofFailure(Exception):
    def __init__(self, expr, assumptions, message):
        self.expr = expr
        self.message = message
        self.assumptions = assumptions

    def __str__(self):
        if len(self.assumptions) == 0:
            assumptionsStr = ""
        else:
            assumptionsStr = " assuming {" + ", ".join(str(assumption) for assumption in self.assumptions) + "}"
        if self.expr is not None:
            return "Unable to prove " + str(self.expr) + assumptionsStr + ":\n" + self.message
        else:
            return "Proof step failed" + assumptionsStr + ":\n" + self.message

class ModusPonensFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)

class InstantiationFailure(ProofFailure):
    def __init__(self, original_known_truth, repl_map, assumptions, message):
        message = "Attempting to instantiate %s with %s:\n%s"%(original_known_truth,
                                                        repl_map, message)
        ProofFailure.__init__(self, None, assumptions, message)

class GeneralizationFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)

class UnusableProof(ProofFailure):
    def __init__(self, provingTheorem, unusableProof, extraMsg=''):
        ProofFailure.__init__(self, unusableProof.provenTruth.expr, [], "Unusable Proof")
        self.provingTheorem = provingTheorem
        self.unusableProof = unusableProof
        self.extraMsg = '; ' + extraMsg

    def __str__(self):
        if self.provingTheorem == self.unusableProof:
            return "Cannot use %s to prove itself"%str(self.provingTheorem)
        if isinstance(self.unusableProof, Theorem) or isinstance(self.unusableProof, Axiom):
            unusuable_proof_str = str(self.unusableProof)
        else:
            unusuable_proof_str = str(self.unusableProof.provenTruth)
        if self.provingTheorem is not None:
            return unusuable_proof_str + ' is not usable while proving ' + str(self.provingTheorem) + ' (it has not been presumed)' + self.extraMsg
        else:
            return 'Cannot use disabled proof for ' + self.unusableItemStr

class CircularLogic(ProofFailure):
    def __init__(self, provingTheorem, presumedTheorem):
        ProofFailure.__init__(self, presumedTheorem.provenTruth.expr, [], "Circular Logic")
        self.provingTheorem = provingTheorem
        self.presumedTheorem = presumedTheorem
    def __str__(self):
        return str(self.presumedTheorem) + ' cannot be presumed while proving ' + str(self.provingTheorem) + ' due to a circular dependence'

class CircularLogicLoop(ProofFailure):
    def __init__(self, presumptionLoop, presumedTheorem):
        assert presumptionLoop[0] == presumptionLoop[-1], "expecting a loop"
        assert str(presumedTheorem) == presumptionLoop[0], "expecting presumedTheorem to match the ends of the presumptionLoop"
        CircularLogic.__init__(self, KnownTruth.theoremBeingProven, presumedTheorem)
        self.presumptionLoop = presumptionLoop
    def __str__(self):
        return "Circular presumption dependency detected: %s"%str(self.presumptionLoop)
