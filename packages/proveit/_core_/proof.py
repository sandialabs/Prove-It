"""
A Proof is a directed, acyclic graph (DAG) that represents the Prove-It
proof for a KnownTruth.  Each object represents a derivation step
(Assumption, ModusPonens, HypotheticalReasoning, Specialization,
or Generalization) and has references to other KnownTruths that
are directly required, each with its Proof.  In this way, the
Proof objects form a DAG.
"""

from proveit._core_.known_truth import KnownTruth
from ._proveit_object_utils import makeUniqueId, addParent
from defaults import defaults, USE_DEFAULTS, WILDCARD_ASSUMPTIONS
from context import Context
import re

class Proof:
    def __init__(self, stepType, provenTruth, requiredTruths):
        # USEFUL FOR TRACKING DERIVED SIDE-EFFECTS
        #if not isinstance(self, Theorem) and not isinstance(self, Axiom):
        #    print "prove", provenTruth.expr
        assert isinstance(provenTruth, KnownTruth)
        self.provenTruth = provenTruth
        self.requiredProofs = [requiredTruth.proof() for requiredTruth in requiredTruths]
        # Is this a usable Proof?  An unusable proof occurs when trying to prove a Theorem
        # that must explicitly presume Theorems that are not fully known in order to
        # avoid circular logic.
        self._unusableTheorem = None # If unusable, this will point to the unusable theorem
                                     # being applied directly or indirectly.
        requiringUnusableTheorem = False
        for requiredProof in self.requiredProofs:
            if requiredProof._unusableTheorem is not None:
                # Mark proofs as unusable when using an "unusable" theorem 
                # directly or indirectly.  Theorems are marked as unusable 
                # when a proof for some Theorem is being generated as a
                # means to avoid circular logic.
                self._unusableTheorem = requiredProof._unusableTheorem
                # Raise an UnusableTheorem expection below (after calling _recordBestProof
                # to indicate the proof even if it isn't usable).
                requiringUnusableTheorem = True
        if not hasattr(self, '_dependents'):
            self._dependents = [] # proofs that directly require this one
        for requiredProof in self.requiredProofs:
            if not hasattr(requiredProof, '_dependents'):
                requiredProof._dependents = []
            requiredProof._dependents.append(self)
        self._step_type = stepType
        # The following is not only a unique representation, but also information to reconstruct the
        # proof step: step type (and mapping information if it is a Specialization), provenTruth, and requiredProofs
        # meaning representations and unique ids are independent of style
        self._meaning_rep = self._generate_unique_rep(lambda obj : hex(obj._meaning_id))
        self._meaning_id = makeUniqueId(self._meaning_rep)
        # style representations and unique ids are dependent of style
        self._style_rep = self._generate_unique_rep(lambda obj : hex(obj._style_id))
        self._style_id = makeUniqueId(self._style_rep)        
        # determine the number of unique steps required for this proof
        self.numSteps = len(self.allRequiredProofs())
        # if it is a Theorem, set its "usability", avoiding circular logic
        if self.isUsable():
            self._setUsability()
        # this new proof may be the first proof, make an old one obselete, or be born obsolete itself.
        hadPreviousProof = (provenTruth.proof() is not None and provenTruth.isUsable())
        provenTruth._recordBestProof(self)
        if requiringUnusableTheorem:
            # Raise an UnusableTheorem exception when an attempt is made 
            # to use an "unusable" theorem directly or indirectly.
            raise UnusableTheorem(KnownTruth.theoremBeingProven, self._unusableTheorem)
        if provenTruth.proof() is self and self.isUsable(): # don't bother with side effects if this proof was born obsolete or unusable
            if not hadPreviousProof: # don't bother with side-effects if this was already proven (and usable); that should have been done already
                # may derive any side-effects that are obvious consequences arising from this truth:
                provenTruth.deriveSideEffects()
        # establish some parent relationships (important in case styles are updated)
        addParent(self.provenTruth, self)
        for requiredProof in self.requiredProofs:
            addParent(requiredProof, self)
        
    def _setUsability(self):
        pass # overloaded for the Theorem type Proof

    def _generate_unique_rep(self, objectRepFn, includeStyle=False):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        return self._generate_step_info(objectRepFn) + '[' + objectRepFn(self.provenTruth) + '];[' + ','.join(objectRepFn(requiredProof) for requiredProof in self.requiredProofs) + ']'

    def _generate_step_info(self, objectRepFn):
        '''
        Generate information about this proof step.
        Overridden by Specialization which also needs to including the mapping information
        and uses the given function to obtain representations of sub-Object.      
        '''
        return self._step_type + ':'

    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of representations
        of Prove-It objects that are referenced.
        '''
        # Skip the step type which is in the beginning and followed by a ':'
        remaining = unique_rep.split(':', 1)[-1]
        # Everything else coming between the punctuation, ';', ':', ',', '{', '}', '[', ']', is a represented object.
        objIds = re.split("\{|\[|,|:|;|\]|\}",remaining) 
        return [objId for objId in objIds if len(objId) > 0]  
                        
    def isUsable(self):
        '''
        Returns True iff this Proof is usable.  A Proof may be unable 
        when trying to prove a Theorem.  Other Theorems must be explicitly 
        presumed, or fully known, in order to avoid circular logic.
        '''
        return self._unusableTheorem is None

    def __eq__(self, other):
        if isinstance(other, Proof):
            return self._meaning_id == other._meaning_id
        else: return False # other must be an Expression to be equal to self
    
    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._meaning_id
    
    def requiredTruths(self):
        '''
        Returns the up-to-date provenTruth objects from the requiredProofs.
        '''
        return [requiredProof.provenTruth for requiredProof in self.requiredProofs]
    
    def usedAxioms(self):
        '''
        Returns the set of axioms that are used directly (not via other theorems) in this proof. 
        '''
        return set().union(*[requiredProof.usedAxioms() for requiredProof in self.requiredProofs])

    def usedTheorems(self):
        '''
        Returns the set of axioms that are used directly (not via other theorems) in this proof. 
        '''
        return set().union(*[requiredProof.usedTheorems() for requiredProof in self.requiredProofs])
        
    def updatedDependents(self):
        self._dependents = [dependent for dependent in self._dependents if dependent.provenTruth._proof is dependent]
        return self._dependents

    def assumptions(self):
        return self.provenTruth.assumptions
        
    def _propagateUnusableTheorem(self, unusableTheorem):
        '''
        Propagate to proofs that are dependent upon an unusable theorem that
        they are unusable due to this unusable theorem.
        '''
        self._unusableTheorem = unusableTheorem
        for dependent in self._dependents:
            dependent._propagateUnusableTheorem(unusableTheorem)        

    def __setattr__(self, attr, value):
        '''
        Proofs should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).  Also,
        _dependents is an exception which can be updated internally.
        '''
        if attr != '_dependents' and attr != '_unusableTheorem' and hasattr(self, attr):
            raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value 
    
    def remake(self):
        '''
        Remake the Proof, using the most up-to-date Proofs for the required truths.
        '''
        raise NotImplementedError('Remake not implemented for ' + str(self.__class__))

    def enumeratedProofSteps(self):
        '''
        Returns a list of Proof objects that includes self and
        all of its direct and indirect requirements.  Duplicates
        will not be included, but they will be presented in an
        order which makes it clear that the dependencies are
        acyclic by making sure requirements come after dependents.
        '''
        from _dependency_graph import orderedDependencyNodes
        return orderedDependencyNodes(self, lambda proof : proof.requiredProofs)
    
    def allRequiredProofs(self):
        '''
        Returns the set of directly or indirectly required proofs.
        '''
        subProofSets = [requiredProof.allRequiredProofs() for requiredProof in self.requiredProofs]
        return set([self]).union(*subProofSets)

    def _repr_html_(self):
        proofSteps = self.enumeratedProofSteps()
        proofNumMap = {proof:k for k, proof in enumerate(proofSteps)}
        html = '<table><tr><th>&nbsp;</th><th>step type</th><th>requirements</th><th>statement</th></tr>\n'
        for k, proof in enumerate(proofSteps):
            html += '<tr><td>%d</td>'%k
            requiredProofNums = ', '.join(str(proofNumMap[requiredProof]) for requiredProof in proof.requiredProofs)
            html += '<td>%s</td><td>%s</td>'%(proof.stepType(), requiredProofNums)
            html += '<td>%s</td>'%proof.provenTruth._repr_html_()
            html += '</tr>\n'
            if isinstance(proof, Specialization):
                html += '<tr><td>&nbsp;</td><td colspan=4 style="text-align:left">' + proof.mappingHTML() + '</td></tr>'
            if isinstance(proof, Axiom) or isinstance(proof, Theorem):
                html += '<tr><td>&nbsp;</td><td colspan=4 style-"text-align:left">'
                html += '<a class="ProveItLink" href="%s">'%proof.getLink() + str(proof.context) + '.' + proof.name + '</a>'
                html += '</td></tr>'
        html += '</table>'
        return html

class Assumption(Proof):
    allAssumptions = dict() # map expression and the to assumption object
     
    def __init__(self, expr, assumptions=None):
        assumptions = defaults.checkedAssumptions(assumptions)
        if expr not in assumptions:
            # an Assumption proof must assume itself; that's what it does.
            assumptions = assumptions + (expr,)
        prev_default_assumptions = defaults.assumptions
        defaults.assumptions = assumptions # these assumptions will be used for deriving any side-effects
        try:
            Proof.__init__(self, 'Assumption', KnownTruth(expr, {expr}, self), [])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions            
        Assumption.allAssumptions[(expr, assumptions)] = self
    
    @staticmethod
    def makeAssumption(expr, assumptions):
        '''
        Return an Assumption object, only creating it if it doesn't
        already exist.  assumptions must already be 'checked' and in
        tuple form.
        '''
        key = (expr, assumptions)
        if key in Assumption.allAssumptions:
            return Assumption.allAssumptions[key]
        return Assumption(expr, assumptions)
        
    def stepType(self):
        return 'assumption'

class Axiom(Proof): 
    def __init__(self, expr, context, name):
        if not isinstance(context, Context):
            raise ValueError("An axiom 'context' must be a Context object")
        if not isinstance(name, str):
            raise ValueError("An axiom 'name' must be a string")
        Proof.__init__(self, 'Axiom', KnownTruth(expr, list(expr.requirements), self), [])
        self.context = context
        self.name = name

    def stepType(self):
        return 'axiom'
    
    def _storedAxiom(self):
        from _context_storage import StoredAxiom
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
        Proof.__init__(self, 'Theorem', KnownTruth(expr, frozenset(), self), [])
        Theorem.allTheorems.append(self)

    def stepType(self):
        return 'theorem'

    def usedTheorems(self):
        return {self}
        
    def __str__(self):
        return self.context.name + '.' + self.name
    
    def containingPrefixes(self):
        '''
        Yields all containing context names and the full theorem name.
        '''
        s = str(self)
        hierarchy = s.split('.')
        for k in xrange(1, len(hierarchy)):
            yield '.'.join(hierarchy[:k])
        yield s
     
    @staticmethod
    def updateUsability():
        for theorem in Theorem.allTheorems:
            theorem._setUsability()            
        
    def _storedTheorem(self):
        from _context_storage import StoredTheorem
        return StoredTheorem(self.context, self.name)

    def getLink(self):
        '''
        Return the HTML link to the theorem proof file.
        '''
        return self._storedTheorem().getProofLink()
    
    def recordPresumingInfo(self, presuming):
        '''
        Record information about what the proof of the theorem
        presumes -- what other theorems/contexts the proof
        is expected to depend upon.
        '''
        self._storedTheorem().recordPresumingInfo(presuming)

    def getRecursivePresumingInfo(self, presumed_theorems, presumed_contexts):
        '''
        Append presumed theorem and context strings to 'presumed_theorems'
        and 'presumed_contexts' respectively.  For each theorem, do this
        recursively.
        '''
        self._storedTheorem().getRecursivePresumingInfo(presumed_theorems, presumed_contexts)        
                
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
                
    def isFullyProven(self, theorem):
        '''
        Returns true if and only if this theorem is fully proven
        (it has a recorded proof and all dependent theorems are fully
        proven, all the way to axioms which don't require proofs).
        '''
        return self._storedTheorem().isComplete()
        
    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or indirectly)
        by the theorem.  Also, if the given theorem is not completely proven,
        return the set of unproven theorems that are required (directly or
        indirectly).  Returns this axiom set and theorem set as a tuple.
        '''
        return self._storedTheorem().allRequirements()

    def allUsedTheorems(self):
        '''
        Returns the set of theorems used to prove the given theorem, directly
        or indirectly.
        '''
        return self._storedTheorem().allUsedTheorems()

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
        Sets the 'usable' attribute to False if a theorem
        is being proven and this theorem is neither presumed
        nor fully proven and independent of the theorem being
        proven.  Sets it to True otherwise.  That is, 
        ensure no circular logic is being employed when 
        proving a theorem.  This applies when a proof has 
        begun (see KnownTruth.beginProof in known_truth.py).  
        When KnownTruth.theoremBeingProven is None, all Theorems are allowed.
        Otherwise only Theorems in the KnownTruth.presuming 
        set (or whose packages is in the KnownTruth.presuming 
        set) or Theorems that have been fully proven with no
        direct/indirect dependence upon KnownTruth.theoremBeingProven
        are allowed.
        '''
        #from proveit.certify import isFullyProven
        if KnownTruth.theoremBeingProven is None:
            self._unusableTheorem = None # Nothing being proven, so all Theorems are usable
            return
        if self in KnownTruth.presumingTheorems or not KnownTruth.presumingPrefixes.isdisjoint(self.containingPrefixes()):
            if self._storedTheorem().presumes(str(KnownTruth.theoremBeingProven)):
                raise CircularLogic(KnownTruth.theoremBeingProven, self)
            self._unusableTheorem = None # This Theorem is usable because it is being presumed.
        else:
            # This Theorem is not usable during the proof (if it is needed, it must be
            # presumed or fully proven).  Propagate this fact to all dependents.
            self._propagateUnusableTheorem(self)

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

def _appendExtraAssumptions(assumptions, knownTruth):
    '''
    When WILDCARD_ASSUMPTIONS ('*') is used, we may need to append 
    extra assumptions needed by the given knownTruth.
    '''
    assumptionsSet = set(assumptions)
    containsWildcard = ('*' in assumptionsSet)
    for assumption in knownTruth.assumptions:
        if assumption not in assumptionsSet:
            if not containsWildcard:
                raise Exception("Should not have missing assumptions at this point unless the wildcard, '*', is being used.")
            assumptions.append(assumption)

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
                # (if WILDCARD_ASSUMPTIONS is included, it will be proven by assumption if there isn't an existing proof otherwise)
                implicationTruth = implicationExpr.prove(assumptions)
                _appendExtraAssumptions(assumptions, implicationTruth)
            except:
                raise ModusPonensFailure(implicationExpr.operands[1], assumptions, 'Implication, %s, is not proven'%str(implicationExpr))
            try:
                # Must prove the antecedent under the given assumptions.
                # (if WILDCARD_ASSUMPTIONS is included, it will be proven by assumption if there isn't an existing proof otherwise)
                antecedentTruth = implicationExpr.operands[0].prove(assumptions)
                _appendExtraAssumptions(assumptions, antecedentTruth)
            except:
                raise ModusPonensFailure(implicationExpr.operands[1], assumptions, 'Antecedent of %s is not proven'%str(implicationExpr))
            # remove any unnecessary assumptions (but keep the order that was provided)
            assumptionsSet = implicationTruth.assumptionsSet | antecedentTruth.assumptionsSet
            assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
            # we have what we need; set up the ModusPonens Proof        
            consequentTruth = KnownTruth(implicationExpr.operands[1], assumptions, self)
            _checkImplication(implicationTruth.expr, antecedentTruth.expr, consequentTruth.expr)
            self.implicationTruth = implicationTruth
            self.antecedentTruth = antecedentTruth
            Proof.__init__(self, 'ModusPonens', consequentTruth, [self.implicationTruth, self.antecedentTruth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def remake(self):
        return ModusPonens(self.implicationTruth.expr, assumptions=self.provenTruth.assumptions)

    def stepType(self):
        return 'modus ponens'

class HypotheticalReasoning(Proof):
    def __init__(self, consequentTruth, antecedentExpr): 
        from proveit.logic import Implies
        assumptions = [assumption for assumption in consequentTruth.assumptions if assumption != antecedentExpr]
        prev_default_assumptions = defaults.assumptions
        defaults.assumptions = assumptions # these assumptions will be used for deriving any side-effects
        try:
            implicationExpr = Implies(antecedentExpr, consequentTruth.expr)
            implicationTruth = KnownTruth(implicationExpr, assumptions, self)
            self.consequentTruth = consequentTruth
            Proof.__init__(self, 'HypotheticalReasoning', implicationTruth, [self.consequentTruth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def remake(self):
        return HypotheticalReasoning(self.consequentTruth, self.provenTruth.expr.antecedent)

    def stepType(self):
        return 'hypothetical reasoning'

class Specialization(Proof):
    def __init__(self, generalTruth, numForallEliminations, specializeMap=None, relabelMap=None, assumptions=USE_DEFAULTS):
        '''
        Create the Specialization proof step that specializes the given general expression
        using the substitution map (subMap) under the given assumptions.  
        Eliminates the number of nested Forall operations as indicated, substituting
        their instance variables according to subMap.  The default for any unspecified instance 
        variable is to specialize it to itself, or, in the case of a bundled variable 
        (Etcetera-wrapped MultiVariables), the default is to specialize it to an empty list.
        Substitution of variables that are not instance variables of the Forall operations
        being eliminated are to be relabeled.  Relabeling is limited to substituting
        a Variable to another Variable or substituting a bundled variable to
        another bundled variable or list of variables (bundled or not).
        '''
        assumptions = list(defaults.checkedAssumptions(assumptions))
        prev_default_assumptions = defaults.assumptions
        defaults.assumptions = assumptions # these assumptions will be used for deriving any side-effects
        try:
            if relabelMap is None: relabelMap = dict()
            if specializeMap is None: specializeMap = dict()
            Failure = SpecializationFailure if numForallEliminations>0 else RelabelingFailure
            if not isinstance(generalTruth, KnownTruth):
                raise Failure(None, [], 'May only specialize/relabel a KnownTruth')
            if generalTruth.proof() is None:
                raise  UnusableTheorem(KnownTruth.theoremBeingProven, generalTruth)
            if not generalTruth.assumptionsSet.issubset(assumptions):
                if '*' in assumptions:
                    # if WILDCARD_ASSUMPTIONS is included, add any extra assumptions that are needed
                    _appendExtraAssumptions(assumptions, generalTruth)
                else:
                    raise Failure(None, [], 'Assumptions do not include the assumptions required by generalTruth')
            generalExpr = generalTruth.expr
            # perform the appropriate substitution/relabeling
            specializedExpr, requirements, mappedVarLists, mappings = Specialization._specialized_expr(generalExpr, numForallEliminations, specializeMap, relabelMap, assumptions)
            # obtain the KnownTruths for the substituted conditions
            requirementTruths = []
            requirementTruthSet = set() # avoid repeats of requirements
            for requirementExpr in requirements:
                try:
                    # each substituted condition must be proven under the assumptions
                    # (if WILDCARD_ASSUMPTIONS is included, it will be proven by assumption if there isn't an existing proof otherwise)
                    requirementTruth = requirementExpr.prove(assumptions)
                    if requirementTruth not in requirementTruthSet:
                        requirementTruths.append(requirementTruth)
                        requirementTruthSet.add(requirementTruth)
                        _appendExtraAssumptions(assumptions, requirementTruth)
                except:
                    raise Failure(specializedExpr, assumptions, 'Unmet specialization requirement: ' + str(requirementExpr))
            # remove any unnecessary assumptions (but keep the order that was provided)
            assumptionsSet = generalTruth.assumptionsSet
            for requirementTruth in requirementTruths:
                assumptionsSet |= requirementTruth.assumptionsSet
            assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
            # we have what we need; set up the Specialization Proof
            self.generalTruth = generalTruth
            self.requirementTruths = requirementTruths
            self.mappedVarLists = mappedVarLists
            self.mappings = mappings
            specializedTruth = KnownTruth(specializedExpr, assumptions, self)
            Proof.__init__(self, 'Specialization', specializedTruth, [generalTruth] + requirementTruths)
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions

    def _generate_step_info(self, objectRepFn):
        '''
        Generate information about this proof step, including mapping information for this specialization.
        '''
        mappingInfo = ';'.join(','.join(objectRepFn(var) + ':' + objectRepFn(self.mappings[var]) for var in mappedVars) \
                                for mappedVars in self.mappedVarLists)
        return self._step_type + ':{' + mappingInfo + '}'
                                
    def remake(self):
        # relabeling variables are the last of the mappedVarLists, preceeding mappedVarLists
        # are for the specializeMap
        numForallEliminations = len(self.mappedVarLists)-1
        specializeMap = {key:self.mappings[key] for varList in self.mappedVarLists[:-1] for key in varList}
        relabelMap = {key:self.mappings[key] for key in self.mappedVarLists[-1]}
        return Specialization(self.generalTruth, numForallEliminations, specializeMap, relabelMap, assumptions = self.provenTruth.assumptions)

    def stepType(self):
        if len(self.mappedVarLists) > 1:
            return 'specialization'
        return 'relabeling' # relabeling only
    
    def mappingHTML(self):
        from proveit import Lambda
        from proveit.logic import Set
        mappedVarLists = self.mappedVarLists
        html = '<span style="font-size:20px;">'
        if len(mappedVarLists) == 1 or (len(mappedVarLists) == 2 and len(mappedVarLists[-1]) == 0):
            # a single relabeling map, or a single specialization map with no relabeling map
            mappedVars = mappedVarLists[0]
            html += ', '.join(Lambda(var, self.mappings[var])._repr_html_() for var in mappedVars)
        else:
            html += ', '.join(Set(*[Lambda(var, self.mappings[var]) for var in mappedVars])._repr_html_() for mappedVars in mappedVarLists[:-1])
            if len(mappedVarLists[-1]) > 0:
                # the last group is the relabeling map, if there is one
                mappedVars = mappedVarLists[-1]
                html += ', relabeling ' + Set(*[Lambda(var, self.mappings[var]) for var in mappedVars])._repr_html_()
        html += '</span>'
        return html

    @staticmethod
    def _specialized_expr(generalExpr, numForallEliminations, specializeMap, relabelMap, assumptions):
        '''
        Return a tuple of (specialization, conditions).  The 
        specialization derives from the given "general" expression and its conditions
        via a specialization inference rule (or relabeling as a special case).
        Eliminates the specified number of Forall operations, substituting all
        of the corresponding instance variables according to the substitution
        map dictionary (subMap), or defaulting basic instance variables as
        themselves. 
        '''
        from proveit import Lambda, Expression, Iter
        from proveit.logic import Forall
        # check that the mappings are appropriate
        for key, sub in relabelMap.items():
            Specialization._checkRelabelMapping(key, sub, assumptions)
            if key==sub: relabelMap.pop(key) # no need to relabel if it is unchanged
        for assumption in assumptions:
            if assumption == WILDCARD_ASSUMPTIONS: continue # ignore the wildcard for this purpose
            if len(assumption.freeVars() & set(relabelMap.keys())) != 0:
                raise RelabelingFailure(None, assumptions, 'Cannot relabel using assumptions that involve any of the relabeling variables')
        
        for key, sub in specializeMap.iteritems():
            if not isinstance(sub, Expression):
                raise TypeError("Expecting specialization substitutions to be 'Expression' objects")
            if key in relabelMap:
                raise SpecializationFailure(None, assumptions, 'Attempting to specialize and relabel the same variable: %s'%str(key))
        
        # Eliminate the desired number of Forall operations and extracted appropriately mapped conditions
        expr = generalExpr
        remainingForallEliminations = numForallEliminations
        partialMap = dict()
        subbedConditions = []
        mappedVarLists = []
        requirements = []
        while remainingForallEliminations>0:
            remainingForallEliminations -= 1
            if not isinstance(expr, Forall):
                raise SpecializationFailure(None, assumptions, 'May only specialize instance variables of directly nested Forall operations')
            lambdaExpr = expr.operand
            assert isinstance(lambdaExpr, Lambda), "Forall Operation lambdaExpr must be a Lambda function"
            instanceVars, expr, conditions  = lambdaExpr.parameterVars, lambdaExpr.body, lambdaExpr.conditions
            # When substituting an iterated instance variable, we need to make sure that the
            # expansion is complete: that there are as many elements of the expansion as
            # the number of elements of the substitution.  For example,
            # x_1, ..., x_n and x -> [a, b, c, d], then x_1, ..., x_n -> a, b, c, d
            # and not a subset.
            for parameter, parameterVar in zip(lambdaExpr.parameters, lambdaExpr.parameterVars):
                subbedParam = None
                if parameterVar in specializeMap: subbedParam = specializeMap[parameterVar]
                elif parameterVar in relabelMap: subbedParam = relabelMap[parameterVar]
                if isinstance(parameter, Iter) and subbedParam is not None:
                    expandedParameter = parameter.substituted(specializeMap, relabelMap, assumptions=assumptions, requirements=requirements)
                    if len(expandedParameter) != len(subbedParam):
                        raise SpecializationFailure(None, assumptions, "Substitution of iterated instance variables incomplete: %d length expansion versus %d length substitution"%(len(expandedParameter), len(subbedParam)))
            mappedVarLists.append(instanceVars)
            # include the mapping for the current instance variables in the partial map
            try:
                partialMap.update({iVar:specializeMap[iVar] for iVar in instanceVars})
            except KeyError:
                raise SpecializationFailure(None, assumptions, 'Must specialize all of the instance variables of the Forall operations to be eliminated')
            # make substitutions in the condition
            subbedConditions += conditions.substituted(partialMap, relabelMap)
                        
        # sort the relabeling vars in order of their appearance in the original expression
        relabelVars = []
        visitedVars = set()
        for var in generalExpr.orderOfAppearance(relabelMap.keys()):
            if var not in visitedVars: # ensure no repeats
                visitedVars.add(var)
                relabelVars.append(var)
        
        mappedVarLists.append(relabelVars) # relabel vars always the last of the mapped variable lists
        mappings = dict(specializeMap)
        mappings.update(relabelMap) # mapping everything
        
        subbed_expr = expr.substituted(specializeMap, relabelMap, assumptions=assumptions, requirements=requirements)
        
        # Return the expression and conditions with substitutions and the information to reconstruct the specialization
        return subbed_expr, subbedConditions + requirements, mappedVarLists, mappings

    @staticmethod
    def _checkRelabelMapping(key, sub, assumptions):
        from proveit import Variable
        if isinstance(key, Variable):
            if not isinstance(sub, Variable):
                raise RelabelingFailure(None, assumptions, 'May only relabel a Variable to a Variable.')
        else:
            raise RelabelingFailure(None, assumptions, "May only relabel a Variable or a MultiVariable")                       

class Generalization(Proof):
    def __init__(self, instanceTruth, newForallVarLists, newConditions=tuple()):
        '''
        A Generalization step wraps a KnownTruth (instanceTruth) in one or more Forall operations.
        The number of Forall operations introduced is the number of lists in newForallVarLists.
        The conditions are introduced in the order they are given at the outermost level that is 
n        applicable.  For example, if newForallVarLists is [[x, y], z]  and the new 
        conditions are f(x, y) and g(y, z) and h(z), this will prove a statement of the form:
            forall_{x, y in Integers | f(x, y)} forall_{z | g(y, z), h(z)} ...
        '''
        from proveit import KnownTruth, Variable
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
            for k, newForallVars in enumerate(reversed(newForallVarLists)):
                for forallVar in newForallVars:
                    if not isinstance(forallVar, Variable):
                        raise ValueError('Forall variables of a generalization must be Variable objects')
                introducedForallVars |= set(newForallVars)
                newConditions = []
                if k == len(newForallVarLists)-1:
                    # the final introduced Forall operation must use all of the remaining conditions
                    newConditions = remainingConditions
                else:
                    # use the first applicable condition and all subsequent conditions in order to maintain the supplied order
                    applicableIndices = [i for i, remainingCondition in enumerate(remainingConditions) if not remainingCondition.freeVars().isdisjoint(newForallVars)]
                    if len(applicableIndices) > 0:
                        j = min(applicableIndices)
                        newConditions = remainingConditions[j:]
                        remainingConditions = remainingConditions[:j]
                # new conditions can eliminate corresponding assumptions
                assumptions -= set(newConditions)
                # create the new generalized expression
                generalizedExpr = Forall(instanceVarOrVars=newForallVars, instanceExpr=expr, conditions=newConditions)
                # make sure this is a proper generalization that doesn't break the logic:
                Generalization._checkGeneralization(generalizedExpr, expr)
                expr = generalizedExpr
            for assumption in assumptions:
                if not assumption.freeVars().isdisjoint(introducedForallVars):
                    raise GeneralizationFailure(generalizedExpr, assumptions, 'Cannot generalize using assumptions that involve any of the new forall variables (except as assumptions are eliminated via conditions or domains)')
            generalizedTruth = KnownTruth(generalizedExpr, assumptions, self)
            self.instanceTruth = instanceTruth
            self.newForallVars = newForallVars
            self.newConditions = newConditions
            Proof.__init__(self, 'Generalization', generalizedTruth, [self.instanceTruth])
        finally:
            # restore the original default assumptions
            defaults.assumptions = prev_default_assumptions
            

    def remake(self):
        return Generalization(self.instanceTruth, self.newForallVars, self.newConditions)

    def stepType(self):
        return 'generalizaton'
    
    @staticmethod
    def _checkGeneralization(generalizedExpr, instanceExpr):
        '''
        Make sure the generalizedExpr is a proper generalization of the instanceExpr.
        '''
        from proveit import Lambda
        from proveit.logic import Forall
        assert isinstance(generalizedExpr, Forall), 'The result of a generalization must be a Forall operation'
        lambdaExpr = generalizedExpr.operand
        assert isinstance(lambdaExpr, Lambda), 'A Forall Expression must be in the proper form'
        expr = lambdaExpr.body
        assert expr == instanceExpr, 'Generalization not consistent with the original expression: ' + str(expr) + ' vs ' + str(instanceExpr)

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
            return "Unable to prove " + str(self.expr) + assumptionsStr + ": " + self.message
        else:            
            return "Proof step failed" + assumptionsStr + ": " + self.message
            
class ModusPonensFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)

class SpecializationFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)

class RelabelingFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)
    
class GeneralizationFailure(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)

class UnusableTheorem(Exception):
    def __init__(self, provingTheorem, unusableTheorem, extraMsg=''):
        self.provingTheorem = provingTheorem
        self.unusableTheorem = unusableTheorem
        self.extraMsg = '; ' + extraMsg
    def __str__(self):
        return str(self.unusableTheorem) + ' is not usable while proving ' + str(self.provingTheorem) + ' (it has not been presumed)' + self.extraMsg

class CircularLogic(Exception):
    def __init__(self, provingTheorem, presumedTheorem):
        self.provingTheorem = provingTheorem
        self.presumedTheorem = presumedTheorem
    def __str__(self):
        return str(self.presumedTheorem) + ' cannot be presumed while proving ' + str(self.provingTheorem) + ' due to a circular dependence'
        