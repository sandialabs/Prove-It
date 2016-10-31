"""
A Proof is a directed, acyclic graph (DAG) that represents the Prove-It
proof for a KnownTruth.  Each object represents a derivation step
(Assumption, ModusPonens, HypotheticalReasoning, Specialization,
or Generalization) and has references to other KnownTruths that
are directly required, each with its Proof.  In this way, the
Proof objects form a DAG.
"""

from proveit._core_.known_truth import KnownTruth
from proveit._core_.expression.expr import ProofFailure
from defaults import defaults
from storage import storage

class Proof:
    def __init__(self, provenTruth, requiredTruths):
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
        # a unique representation for the Proof comprises its provenTruth and requireProofs:
        self._unique_rep = hex(self.provenTruth._unique_id) + ';[' + ','.join(hex(requiredProof._unique_id) for requiredProof in self.requiredProofs) + ']'
        # generate the unique_id based upon hash(unique_rep) but safely dealing with improbable collision events
        self._unique_id = hash(self._unique_rep)
        # in case this new proof makes an old one obselete or is born obsolete itself:
        provenTruth._recordBestProof(self)
        if provenTruth.proof() is self: # don't bother redoing side effects if this proof was born obsolete
            # Axioms and Theorems will derive their side-effects after all of them are created; done in special_statements.py.
            if not isinstance(self, Axiom) and not isinstance(self, Theorem):
                # may derive any side-effects that are obvious consequences arising from this truth:
                provenTruth.deriveSideEffects()

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
        self.dependents = [dependent for dependent in self._dependents if dependent.provenTruth._proof is dependent]
        return self.dependents

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

    def latex(self):
        visited = set()
        proofQueue = [self]
        enumeratedProofs = []
        while len(proofQueue) > 0:
            nextProof = proofQueue.pop(0)
            if nextProof in visited: continue # already showed that one
            visited.add(nextProof)
            enumeratedProofs.append(nextProof)
            proofQueue += nextProof.requiredProofs
        proofNumMap = {proof:k for k, proof in enumerate(enumeratedProofs)}
        outStr = r'\begin{tabular}{rl|l|l|l}' + '\n'
        outStr += r' & \textbf{statement} & \textbf{assumptions} & \textbf{step type} & \textbf{requirements} \\' + '\n'
        for k, proof in enumerate(enumeratedProofs):
            outStr += r'\hline' + '\n'
            outStr += str(k) + '. & $' + proof.provenTruth.expr.latex() + '$ & '
            if isinstance(proof, Axiom) or isinstance(proof, Theorem):
                outStr += r'\multicolumn{3}{|l}{'
                outStr += proof.stepTypeLatex() + ': '
                outStr += proof.package + '.' + proof.name + r'} \\'  + '\n'
            else:
                requiredProofNums = ', '.join(str(proofNumMap[requiredProof]) for requiredProof in proof.requiredProofs)
                outStr += ', '.join(('$' + assumption.latex() + '$') for assumption in proof.assumptions()) \
                    + ' & ' + proof.stepTypeLatex() + ' & ' + requiredProofNums + r' \\' + '\n'
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
        Proof.__init__(self, KnownTruth(expr, {expr}, self), [])
        
    def stepTypeLatex(self):
        return 'assumption'

class Axiom(Proof): 
    def __init__(self, expr, package, name):
        Proof.__init__(self, KnownTruth(expr, frozenset(), self), [])
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
        self._setUsability()
        Proof.__init__(self, KnownTruth(expr, frozenset(), self), [])
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
            raise ModusPonensFailure(self, assumptions, 'Implication is not proven')
        try:
            hypothesisTruth = implicationExpr.operands[0].prove(assumptions)
        except:
            raise ModusPonensFailure('Hypothesis is not proven: ' + str(implicationExpr.operands[0]) + ' assuming {' + ', '.join(str(assumption) for assumption in assumptions) + '}')
        # remove any unnecessary assumptions (but keep the order that was provided)
        assumptionsSet = implicationTruth.assumptionsSet | hypothesisTruth.assumptionsSet
        assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
        # we have what we need; set up the ModusPonens Proof        
        conclusionTruth = KnownTruth(implicationExpr.operands[1], assumptions, self)
        _checkImplication(implicationTruth.expr, hypothesisTruth.expr, conclusionTruth.expr)
        self.implicationTruth = implicationTruth
        self.hypothesisTruth = hypothesisTruth
        Proof.__init__(self, conclusionTruth, [self.implicationTruth, self.hypothesisTruth])

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
        Proof.__init__(self, implicationTruth, [self.conclusionTruth])

    def remake(self):
        return HypotheticalReasoning(self.conclusionTruth, self.provenTruth.expr.hypothesis)

    def stepTypeLatex(self):
        return 'hypothetical reasoning'

class Specialization(Proof):
    def __init__(self, generalExpr, subMap, relabelMap, assumptions=None):
        assumptions = defaults.checkedAssumptions(assumptions)
        Failure = SpecializationFailure if subMap is not None and len(subMap) > 0 else RelabelingFailure
        # obtain the KnownTruth for the general (universally quantified) expression
        try:
            generalTruth = generalExpr.prove(assumptions)
        except:
            raise Failure(self, assumptions, 'Unproven general expression: ' + str(generalExpr))
        # perform the appropriate substitution/relabeling
        specializedExpr, instanceVars, subbedConditions, subMap, relabelMap = Specialization._specialized_expr(generalExpr, assumptions, subMap, relabelMap)
        # obtain the KnownTruths for the substituted conditions
        conditionTruths = []
        for conditionExpr in subbedConditions:
            try:
                # each substituted condition must be proven under the assumptions
                conditionTruths.append(conditionExpr.prove(assumptions))
            except:
                raise Failure(self, assumptions, 'Unmet specialization condition: ' + str(conditionExpr))
        # remove any unnecessary assumptions (but keep the order that was provided)
        assumptionsSet = generalTruth.assumptionsSet
        for conditionTruth in conditionTruths:
            assumptionsSet |= conditionTruth.assumptionsSet
        assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
        # we have what we need; set up the Specialization Proof
        self.generalTruth = generalTruth
        self.conditionTruths = conditionTruths
        self.instanceVars = instanceVars
        self.subMap = subMap
        self.relabelMap = relabelMap
        specializedTruth = KnownTruth(specializedExpr, assumptions, self)
        Proof.__init__(self, specializedTruth, [generalTruth] + conditionTruths)

    def remake(self):
        return Specialization(self.generalTruth.expr, self.subMap, self.relabelMap, assumptions = self.provenTruth.assumptions)

    def stepTypeLatex(self):
        outStr = r'$\begin{array}{l} '
        if self.subMap is not None and len(self.subMap) > 0:
            # use the proper instance Variable order
            iVars = sum([list(iVar.freeVars()) for iVar in self.instanceVars], [])            
            outStr += r'{\rm specialization~via} \\ '
            outStr += r'\left\{' + ',~'.join(iVar.latex() + ': ' + self.subMap[iVar].latex() for iVar in iVars) + r'\right\}'
        if self.relabelMap is not None and len(self.relabelMap) > 0:
            outStr += r'{\rm relabeling~via} \\ '
            outStr += r'\left\{' + ',~'.join(key.latex() + ': ' + val.latex() for key, val in self.relabelMap.iteritems()) + r'\right\}'
        outStr += r'\end{array}$'
        return outStr

    @staticmethod
    def _specialized_expr(generalExpr, assumptions, subMap, relabelMap):
        '''
        State and return a tuple of (specialization, conditions).  The 
        specialization derives from the given original statement and its conditions
        via a specialization inference rule.  It is the specialized form of the 'original' 
        expression by substituting one or more instance variables of outer Forall operations 
        according to the substitution map (subMap) and/or relabeling variables 
        according to the relabeling map (relabelMap).  Unless subMap is empty,
        the outer Forall is eliminated in the process and as a result there may end 
        up being free variables which can be considered to be "arbitrary" variables 
        used in logical reasoning.  Eventually they should be bound again via 
        generalization (the counterpart to specialization).
        '''
        from proveit import Forall, InSet, Expression, Operation, Lambda, Variable, compositeExpression, ExpressionList, ExpressionTensor
        from proveit._core_.expression.composite.composite import Composite
        from proveit._core_.expression.bundle import isBundledVar, isBundledVarOrVar, isBundledOperation
        
        if subMap is None: subMap = dict()
        if relabelMap is None: relabelMap = dict()
        
        # Check the relabelMap and convert Etcetera-wrapped relabelMap keys to Variable keys
        origRelabelItems = list(relabelMap.iteritems())
        relabelMap = dict()
        for key, sub in origRelabelItems:
            if isinstance(key, Variable):
                if not isinstance(sub, Variable):
                    raise RelabelingFailure(None, assumptions, 'May only relabel a Variable to a Variable.')
                relabelVar = key
            elif isBundledVar(key):                
                sub = compositeExpression(sub)
                if not isinstance(sub, ExpressionList):
                    raise RelabelingFailure(None, assumptions, 'May only relabel a Bundled Variable to a single (Bundled) Variable or list of (Bundled) Variables')
                for v in sub:
                    if not isBundledVarOrVar(v) or (isBundledVar(v) and v.multiExprType != key.multiExprType):
                        raise RelabelingFailure(None, assumptions, 'May only relabel a Bundled Variable to Bundled Variables of the same type')
                # change ..x..:expression_or_expressions to x:expressions
                relabelVar = key.bundledExpr
            else:
                raise RelabelingFailure(None, assumptions, "May only relabel a Variable or a Bundled Variable")                       
            relabelMap[relabelVar] = sub
        for assumption in assumptions:
            if len(assumption.freeVars() & set(relabelMap.keys())) != 0:
                raise RelabelingFailure(None, assumptions, 'Cannot relabel using assumptions that involve any of the relabeling variables')        
        # Process the substitution map, performming conversions of Operations and Etcetera-wrapped Operations/Variables
        substitutingVars = set()
        origSubMapItems = list(subMap.iteritems())
        subMap = dict()
        for subKey, sub in origSubMapItems:
            if isinstance(subKey, Variable):
                # substitute a simple Variable
                if not isinstance(sub, Expression) or isinstance(sub, Composite):
                    raise SpecializationFailure(None, assumptions, 'A normal Variable may be not be specialized to a composite Expression (only a Bundled Variable may be)')
                subVar = subKey
                subMap[subVar] = sub
            elif isBundledVar(subKey):
                # substitute an Etcetera-wrapped Variable -- sub in an ExpressionList
                subVar = subKey.bundledExpr
                sub = compositeExpression(sub)
                if sub.__class__ != subKey.multiExprType:
                    if subKey.multiExprType == ExpressionList:
                        raise SpecializationFailure(None, assumptions, 'Etcetera Variables may only be specialized to a list of Expressions')
                    elif subKey.multiExprType == ExpressionTensor:
                        raise SpecializationFailure(None, assumptions, 'Block Variables may only be specialized to a tensor of Expressions')
                    else:
                        raise SpecializationFailure(None, assumptions, 'Unknown Bundle type:' + str(subKey.multiExprType))
                subMap[subVar] = sub
            elif isinstance(subKey, Operation) or isBundledOperation(subKey):
                # Substitute an Operation, f(x):expression, or a Bundled operation like
                # ..Q(x)..:expressions.
                # These get converted in the subMap to a map of the operator Variable
                # to a lambda, e.g. f:(x->expression) or Q:(x->expressions)
                operation = subKey if isinstance(subKey, Operation) else subKey.bundledExpr
                try:
                    if isinstance(subKey, Operation):
                        if not isinstance(sub, Expression) or isinstance(sub, Composite):
                            raise SpecializationFailure(None, assumptions, 'A normal operation may be not be specialized to a composite Expression (only a Bundled Operation may be)')                    
                        lambdaExpr = sub
                        subVar = operation.operator
                        subMap[subVar] = Lambda(operation.operands, lambdaExpr)
                    else: 
                        lambdaExpressions = compositeExpression(sub)
                        subVar = operation.operator #.variable
                        subMap[subVar] = ExpressionList([Lambda(operation.operands, lambdaExpr) for lambdaExpr in lambdaExpressions])
                except TypeError as e:
                    raise SpecializationFailure(None, assumptions, "Improper Operation substitution, error transforming to Lambda: " + e.message)
                except ValueError as e:
                    raise SpecializationFailure(None, assumptions, "Improper Operation substitution, error transforming to Lambda: " + e.message)
            else:
                raise SpecializationFailure(None, assumptions, "Substitution may only map (Bundled) Variable types or (Bundled) Operations that have Variable operators")
            substitutingVars.add(subVar)
        if len(subMap) > 0:
            # an actual Forall specialization
            assert isinstance(generalExpr, Forall), 'May only perform substitution specialization on Forall Expressions (relabeling would be okay)'
            expr = generalExpr.operands
            lambdaExpr = expr['instance_mapping']
            domain = expr['domain'] if 'domain' in expr else None
            assert isinstance(lambdaExpr, Lambda), "Forall Operation bundledExpr must be a Lambda function, or a dictionary mapping 'lambda' to a Lambda function"
            # extract the instance expression and instance variables from the lambda expression        
            instanceVars, expr, conditions  = lambdaExpr.arguments, lambdaExpr.expression['instance_expression'], lambdaExpr.expression['conditions']
            iVarSet = set().union(*[iVar.freeVars() for iVar in instanceVars])
            assert substitutingVars == iVarSet, 'The set of substituting variables must be that same as the set of Forall instance variables'
            for arg in lambdaExpr.arguments:
                if isinstance(arg, Variable) and arg in substitutingVars and isinstance(substitutingVars, ExpressionList):
                    raise SpecializationFailure(None, assumptions, "May only specialize a Forall instance variable with an ExpressionList if it is wrapped in Etcetera")
        else:
            # just a relabeling
            expr = generalExpr
            instanceVars = []
            conditions = ExpressionList([])
            domain = None
        # make substitutions in the condition
        subbedConditions = conditions.substituted(subMap, relabelMap)
        # add conditions for satisfying the domain restriction if there is one
        if domain is not None:
            # extract all of the elements
            for var in instanceVars:
                elementOrList = var.substituted(subMap, relabelMap)
                for element in (elementOrList if isinstance(elementOrList, ExpressionList) else [elementOrList]):
                    subbedConditions.append(InSet(element, domain))
        return expr.substituted(subMap, relabelMap), instanceVars, subbedConditions, subMap, relabelMap

class Generalization(Proof):
    def __init__(self, instanceTruth, newForallVars, newDomain=None, newConditions=tuple()):
        from proveit import Forall, InSet
        # the assumptions required for the generalization are the assumptions of
        # the original KnownTruth minus the all of the new conditions (including those
        # implied by the new domain).
        assumptions = set(instanceTruth.assumptions)
        assumptions -= set(newConditions)
        if newDomain is not None:
            assumptions -= {InSet(forallVar, newDomain) for forallVar in newForallVars}
        instanceExpr = instanceTruth.expr
        generalizedExpr = Forall(instanceVars=newForallVars, instanceExpr=instanceExpr, domain=newDomain, conditions=newConditions)
        for assumption in assumptions:
            if len(assumption.freeVars() & set(newForallVars)) != 0:
                raise GeneralizationFailure(generalizedExpr, assumptions, 'Cannot generalize using assumptions that involve any of the new forall variables unless they are conditions of the generalization')
        Generalization._checkGeneralization(generalizedExpr, instanceExpr)
        generalizedTruth = KnownTruth(generalizedExpr, assumptions, self)
        self.instanceTruth = instanceTruth
        self.newForallVars = newForallVars
        self.newDomain = newDomain
        self.newConditions = newConditions
        Proof.__init__(self, generalizedTruth, [self.instanceTruth])

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
        expr = lambdaExpr.expression['instance_expression']
        assert expr == instanceExpr, 'Generalization not consistent with the original expression: ' + str(expr) + ' vs ' + str(instanceExpr)

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
        