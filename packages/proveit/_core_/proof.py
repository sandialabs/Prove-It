"""
A Proof is a directed, acyclic graph (DAG) that represents the Prove-It
proof for a KnownTruth.  Each object represents a derivation step
(Assumption, ModusPonens, HypotheticalReasoning, Specialization,
or Generalization) and has references to other KnownTruths that
are directly required, each with its Proof.  In this way, the
Proof objects form a DAG.
"""

from proveit._core_.known_truth import KnownTruth
from defaults import defaults, USE_DEFAULTS
from storage import storage, tex_escape
import re

class Proof:
    def __init__(self, stepType, provenTruth, requiredTruths):
        assert isinstance(provenTruth, KnownTruth)
        self.provenTruth = provenTruth
        self.requiredProofs = [requiredTruth.proof() for requiredTruth in requiredTruths]
        # Is this a usable Proof?  An unusable proof occurs when trying to prove a Theorem
        # that must explicitly presume Theorems that are not fully known in order to
        # avoid circular logic.
        self._unusableTheorem = None # If unusable, this will point to the unusable theorem
                                     # being applied directly or indirectly.
        for requiredProof in self.requiredProofs:
            if requiredProof._unusableTheorem is not None:
                # Mark proofs as unusable when using an "unusable" theorem 
                # directly or indirectly.  Theorems are marked as unusable 
                # when a proof for some Theorem is being generated as a
                # means to avoid circular logic.
                self._unusableTheorem = requiredProof._unusableTheorem
                if len(KnownTruth.in_progress_to_derive_sideeffects) == 0:
                    # When not deriving a side-effect, raise an UnusableTheorem
                    # exception when an attempt is made to use an "unusable" theorem
                    # directly or indirectly.
                    raise UnusableTheorem(KnownTruth.theoremBeingProven, self._unusableTheorem)
        self.numSteps = sum(proof.numSteps for proof in self.requiredProofs) + 1
        if not hasattr(self, '_dependents'):
            self._dependents = [] # proofs that directly require this one
        for requiredProof in self.requiredProofs:
            if not hasattr(requiredProof, '_dependents'):
                requiredProof._dependents = []
            requiredProof._dependents.append(self)
        self._step_type = stepType
        # The following is not only a unique representation, but also information to reconstruct the
        # proof step: step type (and mapping information if it is a Specialization), provenTruth, and requiredProofs
        self._unique_rep = self._generate_unique_rep(lambda expr : hex(expr._unique_id))
        # generate the unique_id based upon hash(unique_rep) but safely dealing with improbable collision events
        self._unique_id = hash(self._unique_rep)
        # in case this new proof makes an old one obselete or is born obsolete itself:
        provenTruth._recordBestProof(self)
        if provenTruth.proof() is self: # don't bother redoing side effects if this proof was born obsolete
            # Axioms and Theorems will derive their side-effects after all of them are created; done in special_statements.py.
            if not isinstance(self, Axiom) and not isinstance(self, Theorem):
                # may derive any side-effects that are obvious consequences arising from this truth:
                provenTruth.deriveSideEffects()

    def _generate_unique_rep(self, objectRepFn):
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
    def _referencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of representations
        of Prove-It objects that are referenced.
        '''
        # Skip the step type which is in the beginning and followed by a ':'
        remaining = unique_rep.split(':', 1)[-1]
        # Everything else that between the punctuation, ';', ':', ',', '{', '}', '[', ']' is a represented object.
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
            return self._unique_id == other._unique_id
        else: return False # other must be an KnownTruth to be equal to self
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return self._unique_id
    
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
        # proofsWithRepeats with the required proofs.  Allow duplicates in a first
        # pass.  Remove the duplicates in a second pass.
        proofQueue = [self]
        proofsWithRepeats = []
        while len(proofQueue) > 0:
            nextProof = proofQueue.pop(0)
            proofsWithRepeats.append(nextProof)
            proofQueue += nextProof.requiredProofs
        # Second pass: remove duplicates.  Requirements should always come later 
        # (presenting the graph in a way that guarantees that it is acyclic).
        visited = set()
        proofSteps = []
        for proof in reversed(proofsWithRepeats):
            if proof in visited:
                continue
            proofSteps.insert(0, proof)
            visited.add(proof)
        return proofSteps        

    def latex(self):
        proofSteps = self.enumeratedProofSteps()
        proofNumMap = {proof:k for k, proof in enumerate(proofSteps)}
        outStr = r'\begin{tabular}{rl|l|l|l}' + '\n'
        outStr += r' & \textbf{statement} & \textbf{assumptions} & \textbf{step type} & \textbf{requirements} \\' + '\n'
        for k, proof in enumerate(proofSteps):
            outStr += r'\hline' + '\n'
            outStr += str(k) + '. & $' + proof.provenTruth.expr.latex() + '$ & '
            if isinstance(proof, Axiom) or isinstance(proof, Theorem):
                outStr += r'\multicolumn{3}{|l}{'
                outStr += proof.stepTypeLatex() + ': '
                outStr += tex_escape(proof.package) + '.' + tex_escape(proof.name) + r'} \\'  + '\n'
            else:
                requiredProofNums = ', '.join(str(proofNumMap[requiredProof]) for requiredProof in proof.requiredProofs)
                outStr += ', '.join(('$' + assumption.latex() + '$') for assumption in proof.assumptions()) \
                    + ' & ' + proof.stepTypeLatex() + ' & ' + requiredProofNums + r' \\' + '\n'
            if isinstance(proof, Specialization):
                outStr += r'\hline' + '\n'
                outStr += r' & \multicolumn{4}{c}{' + proof.mappingLatex() + r'} \\' + '\n'
        outStr += r'\hline' + '\n'
        outStr += r'\end{tabular}' + '\n'
        return outStr

    def _repr_png_(self):
        if (not hasattr(self,'png') or self.png is None):
            try:
                self.png = storage._retrieve_png(self, self.latex(), self._config_latex_tool)
            except:
                return None # No png if it isn't proven
        return self.png # previous stored or generated
        
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.provenTruth._config_latex_tool(lt)   
        for assumption in self.assumptions():
            assumption._config_latex_tool(lt)
        for requiredProof in self.requiredProofs():
            requiredProof._config_latex_tool(lt)

class Assumption(Proof): 
    def __init__(self, expr):
        Proof.__init__(self, 'Assumption', KnownTruth(expr, {expr}, self), [])
        
    def stepTypeLatex(self):
        return 'assumption'

class Axiom(Proof): 
    def __init__(self, expr, package, name):
        Proof.__init__(self, 'Axiom', KnownTruth(expr, frozenset(), self), [])
        self.package = package
        self.name = name

    def stepTypeLatex(self):
        return 'axiom'
    
    def usedAxioms(self):
        return {self}

    def __str__(self):
        return self.package + '.' + self.name
        
class Theorem(Proof): 
    allTheorems = []
    
    def __init__(self, expr, package, name):
        if not isinstance(package, str):
            raise ValueError("A theorem 'package' must be a string")
        if not isinstance(name, str):
            raise ValueError("A theorem 'name' must be a string")
        self.package = package
        self.name = name
        # keep track of proofs that may be used to prove the theorem
        # before 'beginProof' is called so we will have the proof handy.
        self._possibleProofs = []
        Proof.__init__(self, 'Theorem', KnownTruth(expr, frozenset(), self), [])
        self._setUsability()
        Theorem.allTheorems.append(self)

    def stepTypeLatex(self):
        return 'theorem'

    def usedTheorems(self):
        return {self}
        
    def __str__(self):
        return self.package + '.' + self.name
    
    def containingPackages(self):
        '''
        Yields the packages that contain this Theorem at all levels
        of the hierarchy; includes the full theorem name
        (as the deepest level "package").
        '''
        s = str(self)
        hierarchy = s.split('.')
        for k in xrange(len(hierarchy)):
            yield '.'.join(hierarchy[:k])
     
    @staticmethod
    def updateUsability():
        for theorem in Theorem.allTheorems:
            theorem._setUsability()
            if theorem._unusableTheorem is not None:
                # propagate the fact that this proof is not usable
                theorem.provenTruth._updateProof(None)
    
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
        from proveit.certify import isFullyProven
        if KnownTruth.theoremBeingProven is None:
            self._unusableTheorem = None # Nothing being proven, so all Theorems are usable
            return
        if self in KnownTruth.presumingTheorems or not KnownTruth.presumingPackages.isdisjoint(self.containingPackages()):
            if self in KnownTruth.dependentTheoremsOfTheoremBeingProven:
                raise CircularLogic(KnownTruth.theoremBeingProven, self)
            self._unusableTheorem = None # This Theorem is usable because it is being presumed.
        elif isFullyProven(self) and self != KnownTruth.theoremBeingProven and self not in KnownTruth.dependentTheoremsOfTheoremBeingProven:
            self._unusableTheorem = None # This Theorem is usable because it has been fully proven as does not depend upon the Theorem being proven.
        else:
            # This Theorem is not usable during the proof (if it is needed, it must be
            # presumed or fully proven).
            self._unusableTheorem = self

def _checkImplication(implicationExpr, hypothesisExpr, conclusionExpr):
    '''
    Make sure the implicationExpr is a proper implication with
    hypothesisExpr as the hypothesis and conclusionExpr as the conclusion.
    '''
    from proveit import Implies
    assert isinstance(implicationExpr, Implies),  'The result of hypothetical reasoning must be an Implies operation'
    assert len(implicationExpr.operands)==2, 'Implications are expected to have two operands'
    assert hypothesisExpr==implicationExpr.operands[0], 'The result of hypothetical reasoning must be an Implies operation with the proper hypothesis'
    assert conclusionExpr==implicationExpr.operands[1], 'The result of hypothetical reasoning must be an Implies operation with the proper conclusion'

class ModusPonens(Proof):
    def __init__(self, implicationExpr, assumptions=None):
        from proveit import Implies
        assumptions = defaults.checkedAssumptions(assumptions)
        # obtain the implication and hypothesis KnownTruths
        assert isinstance(implicationExpr, Implies) and len(implicationExpr.operands)==2, 'The implication of a modus ponens proof must refer to an Implies expression with two operands'
        try:
            implicationTruth = implicationExpr.prove(assumptions)
        except:
            raise ModusPonensFailure(implicationExpr.operands[1], assumptions, 'Implication, %s, is not proven'%str(implicationExpr))
        try:
            hypothesisTruth = implicationExpr.operands[0].prove(assumptions)
        except:
            raise ModusPonensFailure(implicationExpr.operands[1], assumptions, 'Hypothesis of %s is not proven'%str(implicationExpr))
        # remove any unnecessary assumptions (but keep the order that was provided)
        assumptionsSet = implicationTruth.assumptionsSet | hypothesisTruth.assumptionsSet
        assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
        # we have what we need; set up the ModusPonens Proof        
        conclusionTruth = KnownTruth(implicationExpr.operands[1], assumptions, self)
        _checkImplication(implicationTruth.expr, hypothesisTruth.expr, conclusionTruth.expr)
        self.implicationTruth = implicationTruth
        self.hypothesisTruth = hypothesisTruth
        Proof.__init__(self, 'ModusPonens', conclusionTruth, [self.implicationTruth, self.hypothesisTruth])

    def remake(self):
        return ModusPonens(self.implicationTruth.expr, assumptions=self.provenTruth.assumptions)

    def stepTypeLatex(self):
        return 'modus ponens'

class HypotheticalReasoning(Proof):
    def __init__(self, conclusionTruth, hypothesisExpr): 
        from proveit import Implies
        assumptions = [assumption for assumption in conclusionTruth.assumptions if assumption != hypothesisExpr]
        implicationExpr = Implies(hypothesisExpr, conclusionTruth.expr)
        implicationTruth = KnownTruth(implicationExpr, assumptions, self)
        self.conclusionTruth = conclusionTruth
        Proof.__init__(self, 'HypotheticalReasoning', implicationTruth, [self.conclusionTruth])

    def remake(self):
        return HypotheticalReasoning(self.conclusionTruth, self.provenTruth.expr.hypothesis)

    def stepTypeLatex(self):
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
        being eliminated or to be relabeled.  Relabeling is limited to substituting
        a Variable to another Variable or substituting a bundled variable to
        another bundled variable or list of variables (bundled or not).
        '''
        assumptions = defaults.checkedAssumptions(assumptions)
        if relabelMap is None: relabelMap = dict()
        if specializeMap is None: specializeMap = dict()
        Failure = SpecializationFailure if numForallEliminations>0 else RelabelingFailure
        if not isinstance(generalTruth, KnownTruth):
            raise Failure(None, [], 'May only specialize/relabel a KnownTruth')
        if not generalTruth.assumptionsSet.issubset(assumptions):
            raise Failure(None, [], 'Assumptions do not include the assumptions required by generalTruth')
        generalExpr = generalTruth.expr
        # perform the appropriate substitution/relabeling
        specializedExpr, subbedConditions, mappedVarLists, mappings = Specialization._specialized_expr(generalExpr, numForallEliminations, specializeMap, relabelMap, assumptions)
        # obtain the KnownTruths for the substituted conditions
        conditionTruths = []
        for conditionExpr in subbedConditions:
            try:
                # each substituted condition must be proven under the assumptions
                conditionTruths.append(conditionExpr.prove(assumptions))
            except:
                raise Failure(specializedExpr, assumptions, 'Unmet specialization condition: ' + str(conditionExpr))
        # remove any unnecessary assumptions (but keep the order that was provided)
        assumptionsSet = generalTruth.assumptionsSet
        for conditionTruth in conditionTruths:
            assumptionsSet |= conditionTruth.assumptionsSet
        assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
        # we have what we need; set up the Specialization Proof
        self.generalTruth = generalTruth
        self.conditionTruths = conditionTruths
        self.mappedVarLists = mappedVarLists
        self.mappings = mappings
        specializedTruth = KnownTruth(specializedExpr, assumptions, self)
        Proof.__init__(self, 'Specialization', specializedTruth, [generalTruth] + conditionTruths)

    def _generate_step_info(self, objectRepFn):
        '''
        Generate information about this proof step, including mapping information for this specialization.
        '''
        mappingInfo = ';'.join(','.join(objectRepFn(var) + ':' + objectRepFn(self.mappings[var]) for var in mappedVars) \
                                for mappedVars in self.mappedVarLists)
        return self._step_type + ':{' + mappingInfo + '}'
                                
    def remake(self):
        return Specialization(self.generalTruth.expr, self.subMap, self.relabelMap, assumptions = self.provenTruth.assumptions)

    def stepTypeLatex(self):
        if len(self.mappedVarLists) > 1:
            return 'specialization'
        return 'relabeling' # relabeling only
    
    def mappingLatex(self):
        mappedVarLists = list(self.mappedVarLists)
        if len(mappedVarLists[-1]) == 0:
            # drop the last semicolon if no relabeling is necessary
            mappedVarLists.pop()
        outStr = r'$ \left\{' 
        outStr += ' ;~'.join(',~'.join(var.latex() + ' : ' + self.mappings[var].latex() for var in mappedVars) \
                            for mappedVars in mappedVarLists)
        outStr += r'\right\} $'
        return outStr

    @staticmethod
    def _specialized_expr(generalExpr, numForallEliminations, specializeMap, relabelMap, assumptions):
        '''
        Return a tuple of (specialization, conditions).  The 
        specialization derives from the given "general" expression and its conditions
        via a specialization inference rule (or relabeling as a special case).
        Eliminates the specified number of Forall operations, substituting all
        of the corresponding instance variables according to the substitution
        map dictionary (subMap), or defaulting basic instance variables as
        themselves or bundled instance variables (Etcetera-wrapped or Block-wrapped 
        MultiVariables) as empty lists. 
        '''
        from proveit import Forall, InSet, Lambda, ExpressionList
        
        # check that the mappings are appropriate
        for key, sub in relabelMap.items():
            Specialization._checkRelabelMapping(key, sub, assumptions)
            if key==sub: relabelMap.pop(key) # no need to relabel if it is unchanged
        for assumption in assumptions:
            if len(assumption.freeVars() & set(relabelMap.keys())) != 0:
                raise RelabelingFailure(None, assumptions, 'Cannot relabel using assumptions that involve any of the relabeling variables')

        for key, sub in specializeMap.iteritems():
            Specialization._checkSpecializeMapping(key, sub, assumptions)
            if key in relabelMap:
                raise SpecializationFailure(None, assumptions, 'Attempting to specialize and relabel the same variable: %s'%str(key))
        
        # Eliminate the desired number of Forall operations and extracted appropriately mapped conditions
        expr = generalExpr
        remainingForallEliminations = numForallEliminations
        partialMap = dict()
        subbedConditions = []
        mappedVarLists = []
        while remainingForallEliminations>0:
            remainingForallEliminations -= 1
            if not isinstance(expr, Forall):
                raise SpecializationFailure(None, assumptions, 'May only specialize instance variables of directly nested Forall operations')
            expr = expr.operands
            domain = expr['domain'] if 'domain' in expr else None
            lambdaExpr = expr['instance_mapping'];
            assert isinstance(lambdaExpr, Lambda), "Forall Operation lambdaExpr must be a Lambda function"
            instanceVars, expr, conditions  = lambdaExpr.parameters, lambdaExpr.body['instance_expression'], lambdaExpr.body['conditions']
            mappedVarLists.append(instanceVars)
            # include the mapping for the current instance variables in the partial map
            try:
                partialMap.update({iVar:specializeMap[iVar] for iVar in instanceVars})
            except KeyError:
                raise SpecializationFailure(None, assumptions, 'Must specialize all of the instance variables of the Forall oeprations to be eliminated')
            # make substitutions in the condition
            subbedConditions += conditions.substituted(partialMap, relabelMap)
            # add conditions for satisfying the domain restriction if there is one
            if domain is not None:
                # extract all of the elements
                for iVar in instanceVars:
                    elementOrList = iVar.substituted(partialMap, relabelMap)
                    for element in (elementOrList if isinstance(elementOrList, ExpressionList) else [elementOrList]):
                        subbedConditions.append(InSet(element, domain.substituted(partialMap, relabelMap)))
                        
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
        
        # Return the expression and conditions with substitutions and the information to reconstruct the specialization
        return expr.substituted(specializeMap, relabelMap), subbedConditions, mappedVarLists, mappings

    @staticmethod
    def _checkRelabelMapping(key, sub, assumptions):
        from proveit import Variable, MultiVariable, Composite, ExpressionList
        if isinstance(key, Variable):
            if not isinstance(sub, Variable):
                raise RelabelingFailure(None, assumptions, 'May only relabel a Variable to a Variable.')
        elif isinstance(key, MultiVariable):
            if isinstance(sub, ExpressionList):
                elems = sub
            elif isinstance(sub, Composite):
                elems = sub.values()
            else:
                raise RelabelingFailure(None, assumptions, 'May only relabel a MultiVariable to a Composite Expression (as a convention)')                
            for elem in elems:
                if not isinstance(elem, Variable) and not isinstance(sub, MultiVariable):
                    raise RelabelingFailure(None, assumptions, 'May only relabel a MultiVariable to a Composite of Variables/MultiVariables')
        else:
            raise RelabelingFailure(None, assumptions, "May only relabel a Variable or a MultiVariable")                       

    @staticmethod
    def _checkSpecializeMapping(key, sub, assumptions):
        from proveit import Expression, Composite, Variable, MultiVariable
        if isinstance(key, Variable):
            # substitute a simple Variable
            if not isinstance(sub, Expression) or isinstance(sub, Composite):
                raise SpecializationFailure(None, assumptions, 'A normal Variable may be not be specialized to a composite Expression (only a MultiVariable may be)')
        elif isinstance(key, MultiVariable):
            if sub != key and not isinstance(sub, Composite):
                raise SpecializationFailure(None, assumptions, 'A MultiVariable may only be specialized to a composite expression (or itself)')
        else:
            raise SpecializationFailure(None, assumptions, "May only specialize Forall instance Variables/MultiVariables")


class Generalization(Proof):
    def __init__(self, instanceTruth, newForallVarLists, newDomains, newConditions=tuple()):
        '''
        A Generalization step wraps a KnownTruth (instanceTruth) in one or more Forall operations.
        The number of Forall operations introduced is the number of lists in newForallVarLists
        and the number of elements in newDomains.  The conditions are introduced in the
        order they are given at the outermost level that is applicable.  For example,
        if newForallVarLists is [[x, y], z], the newDomains are Integers and Reals, and the new 
        conditions are f(x, y) and g(y, z) and h(z), this will prove a statement of the form:
            forall_{x, y in Integers | f(x, y)} forall_{z in Reals | g(y, z), h(z)} ...
        '''
        from proveit import KnownTruth, Forall, Variable, InSet
        if not isinstance(instanceTruth, KnownTruth):
            raise GeneralizationFailure(None, [], 'May only generalize a KnownTruth instance')
        # the assumptions required for the generalization are the assumptions of
        # the original KnownTruth minus the all of the new conditions (including those
        # implied by the new domain).
        assumptions = set(instanceTruth.assumptions)
        remainingConditions = list(newConditions)
        expr = instanceTruth.expr
        introducedForallVars = set()
        if len(newForallVarLists) != len(newDomains):
            raise GeneralizationFailure(None, assumptions, 'The number of forall variable lists and new domains does not match: %d vs %d'%(len(newForallVarLists), len(newDomains)))
        for k, (newForallVars, newDomain) in enumerate(reversed(zip(newForallVarLists, newDomains))):
            for forallVar in newForallVars:
                if not isinstance(forallVar, Variable):
                    raise GeneralizationFailure(None, assumptions, 'Forall variables of a generalization must be Variable objects')
            introducedForallVars |= set(newForallVars)
            newConditions = []
            if k == len(newForallVarLists):
                # the final introduced Forall operation must use all of the remaining conditions
                newConditions = remainingConditions
            else:
                while len(remainingConditions) > 0 and not remainingConditions[-1].freeVars().isdisjoint(newForallVars):
                    # This condition is applicable since one (or more) of its free variables is 
                    # occurs as a new forall variable.
                    newConditions.insert(0, remainingConditions.pop())            
            # new conditions and domain can eliminate corresponding assumptions
            assumptions -= set(newConditions)
            if newDomain is not None:
                assumptions -= {InSet(forallVar, newDomain) for forallVar in newForallVars}
            # create the new generalized expression
            generalizedExpr = Forall(instanceVars=newForallVars, instanceExpr=expr, domain=newDomain, conditions=newConditions)
            # make sure this is a proper generalization that doesn't break the logic:
            Generalization._checkGeneralization(generalizedExpr, expr)
            expr = generalizedExpr
        for assumption in assumptions:
            if not assumption.freeVars().isdisjoint(introducedForallVars):
                raise GeneralizationFailure(generalizedExpr, assumptions, 'Cannot generalize using assumptions that involve any of the new forall variables (except as assumptions are eliminated via conditions or domains)')
        generalizedTruth = KnownTruth(generalizedExpr, assumptions, self)
        self.instanceTruth = instanceTruth
        self.newForallVars = newForallVars
        self.newDomain = newDomain
        self.newConditions = newConditions
        Proof.__init__(self, 'Generalization', generalizedTruth, [self.instanceTruth])

    def remake(self):
        return Generalization(self.instanceTruth, self.newForallVars, self.newDomain, self.newConditions)

    def stepTypeLatex(self):
        return 'generalizaton'
    
    @staticmethod
    def _checkGeneralization(generalizedExpr, instanceExpr):
        '''
        Make sure the generalizedExpr is a proper generalization of the instanceExpr.
        '''
        from proveit import Forall, Lambda
        assert isinstance(generalizedExpr, Forall), 'The result of a generalization must be a Forall operation'
        operands = generalizedExpr.operands
        lambdaExpr = operands['instance_mapping']
        assert isinstance(lambdaExpr, Lambda), 'A Forall Expression must be in the proper form'
        expr = lambdaExpr.body['instance_expression']
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
    def __init__(self, provingTheorem, unusableTheorem):
        self.provingTheorem = provingTheorem
        self.unusableTheorem = unusableTheorem
    def __str__(self):
        return str(self.unusableTheorem) + ' is not usable while proving ' + str(self.provingTheorem) + ' (it has not be presumed)'

class CircularLogic(Exception):
    def __init__(self, provingTheorem, presumedTheorem):
        self.provingTheorem = provingTheorem
        self.presumedTheorem = presumedTheorem
    def __str__(self):
        return str(self.presumedTheorem) + ' cannot be presumed while proving ' + str(self.provingTheorem) + ' due to a circular dependence'
        