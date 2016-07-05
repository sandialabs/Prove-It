"""
A Proof is a directed, acyclic graph (DAG) that represents the Prove-It
proof for a KnownTruth.  Each object represents a derivation step
(Assumption, ModusPonens, HypotheticalReasoning, Specialization,
or Generalization) and has references to other KnownTruths that
are directly required, each with its Proof.  In this way, the
Proof objects form a DAG.
"""

from proveit._core_.known_truth import KnownTruth
from proveit._core_.defaults_and_settings import defaults, storage

class Proof:
    def __init__(self, provenTruth, requiredTruths):
        assert isinstance(provenTruth, KnownTruth)
        self.provenTruth = provenTruth
        self.requiredProofs = [requiredTruth.proof() for requiredTruth in requiredTruths]
        self._dependents = [] # proofs that directly require this one
        for requiredProof in self.requiredProofs:
            requiredProof._dependents.append(requiredProof)

    def requiredTruths(self):
        return [requiredProof.provenTruth for requiredProof in self.requiredProofs]

    def assumptions(self):
        return self.provenTruth.assumptions

    def __setattr__(self, attr, value):
        '''
        Proofs should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).  Also,
        _dependents is an exception which can be updated internally.
        '''
        if attr != '_dependents' and hasattr(self, attr):
            raise Exception("Attempting to alter read-only value")
        self.__dict__[attr] = value 

    def updated(self):
        '''
        If any of the provenTruths in the directed acyclic graph of proof objects have
        been replaced (made obsolete), a new Proof will be returned which uses the replacements.
        '''
        requiredProofs = [requiredProof.provenTruth.proof() for requiredProof in self.requiredProofs]
        if requiredProofs != self.requiredProofs:
            return Proof(self.provenTruth, [requiredProof.provenTruth for requiredProof in requiredProofs])
        return self

    def latex(self, latexTool=None):
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
        for k, proof in enumerate(proofNumMap):
            if latexTool is not None:
                proof.provenTruth.expr()._config_latex_tool(latexTool)
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
                self.png = storage._retrieve_png(self, self._generate_png)
            except:
                return None # No png if it isn't proven
        return self.png # previous stored or generated
    
    def _generate_png(self):
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        LaTeXTool.clear_instance()
        lt = LaTeXTool.instance()
        lt.use_breqn = False
        self._config_latex_tool(lt)
        return latex_to_png(self.latex(), backend='dvipng', wrap=True)
    
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.provenTruth._config_latex_tool(lt)    

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

class Theorem(Proof): 
    def __init__(self, expr, package, name):
        Proof.__init__(self, KnownTruth(expr, frozenset(), self), [])
        self.package = package
        self.name = name

    def stepTypeLatex(self):
        return 'theorem'

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
        if assumptions is None: assumptions = defaults.assumptions        
        # obtain the implication and hypothesis KnownTruths
        assert isinstance(implicationExpr, Implies) and len(implicationExpr.operands)==2, 'The implication of a modus ponens proof must refer to an Implies expression with two operands'
        try:
            implicationTruth = implicationExpr.prove(assumptions)
        except:
            raise ModusPonensFailure('Implication is not proven: ' + str(implicationExpr)) + ' assuming ' + ', '.join(assumption for assumption in assumptions)
        try:
            hypothesisTruth = implicationExpr.operands[0].prove(assumptions)
        except:
            raise ModusPonensFailure('Hypothesis is not proven: ' + str(implicationExpr)) + ' assuming ' + ', '.join(assumption for assumption in assumptions)
        # remove any unnecessary assumptions (but keep the order that was provided)
        assumptionsSet = implicationTruth.assumptionsSet | hypothesisTruth.assumptionsSet
        assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
        # we have what we need; set up the ModusPonens Proof        
        conclusionTruth = KnownTruth(implicationExpr.operands[1], assumptions, self)
        _checkImplication(implicationTruth.expr, hypothesisTruth.expr, conclusionTruth.expr)
        self.implicationTruth = implicationTruth
        self.hypothesisTruth = hypothesisTruth
        Proof.__init__(self, conclusionTruth, [self.implicationTruth, self.hypothesisTruth])

    def stepTypeLatex(self):
        return 'modus ponens'

class HypotheticalReasoning(Proof):
    def __init__(self, conclusionTruth, hypothesisExpr): 
        from proveit import Implies
        assumptions = conclusionTruth.assumptions - {hypothesisExpr}
        implicationExpr = Implies(hypothesisExpr, conclusionTruth.expr)
        implicationTruth = KnownTruth(implicationExpr, assumptions, self)
        self.conclusionTruth = conclusionTruth
        Proof.__init__(self, implicationTruth, [self.conclusionTruth])

    def stepTypeLatex(self):
        return 'hypothetical reasoning'

class Specialization(Proof):
    def __init__(self, generalExpr, subMap, relabelMap, assumptions=None):
        if assumptions is None: assumptions = defaults.assumptions
        # obtain the KnownTruth for the general (universally quantified) expression
        try:
            generalTruth = generalExpr.prove(assumptions)
        except:
            raise SpecializationFailure('Unproven general expression: ' + str(generalExpr) + ' assuming {' + ', '.join(assumption for assumption in assumptions) + '}')
        # perform the appropriate substitution/relabeling
        specializedExpr, subbedConditions, subMap, relabelMap = Specialization._specialized_expr(generalExpr, subMap, relabelMap)
        # obtain the KnownTruths for the substituted conditions
        conditionTruths = []
        for conditionExpr in subbedConditions:
            try:
                # each substituted condition must be proven under the assumptions
                conditionTruths.append(conditionExpr.prove(assumptions))
            except:
                raise SpecializationFailure('Unmet specialization condition: ' + str(conditionExpr) + ' assuming {' + ', '.join(assumption for assumption in assumptions) + '}')
        # remove any unnecessary assumptions (but keep the order that was provided)
        assumptionsSet = generalTruth.assumptionsSet
        for conditionTruth in conditionTruths:
            assumptionsSet |= conditionTruth.assumptionsSet
        assumptions = [assumption for assumption in assumptions if assumption in assumptionsSet]
        # we have what we need; set up the Specialization Proof
        self.generalTruth = generalTruth
        self.conditionTruths = conditionTruths
        self.subMap = subMap
        self.relabelMap = relabelMap
        specializedTruth = KnownTruth(specializedExpr, assumptions, self)
        Proof.__init__(self, specializedTruth, [generalTruth] + conditionTruths)

    def stepTypeLatex(self):
        outStr = r'$\begin{array}{l} '
        if self.subMap is not None and len(self.subMap) > 0:
            outStr += r'{\rm specialization~via} \\ '
            outStr += r'\left\{' + ',~'.join(key.latex() + ': ' + val.latex() for key, val in self.subMap) + r'\right\}'
        if self.relabelMap is not None and len(self.relabelMap) > 0:
            outStr += r'{\rm relabeling via} \\ '
            outStr += r'\left\{' + ',~'.join(key.latex() + ': ' + val.latex() for key, val in self.relabelMap) + r'\right\}'
        outStr += r'\end{array}$'
        return outStr

    @staticmethod
    def _specialized_expr(generalExpr, subMap, relabelMap):
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
        
        # Check the relabelMap and convert Etcetera-wrapped relabelMap keys to Variable keys
        origRelabelItems = list(relabelMap.iteritems())
        relabelMap = dict()
        for key, sub in origRelabelItems:
            if isinstance(key, Variable):
                if not isinstance(sub, Variable):
                    raise SpecializationFailure('May only relabel a Variable to a Variable.')
                relabelVar = key
            elif isBundledVar(key):                
                sub = compositeExpression(sub)
                if not isinstance(sub, ExpressionList):
                    raise SpecializationFailure('May only relabel a Bundled Variable to a single (Bundled) Variable or list of (Bundled) Variables')
                for v in sub:
                    if not isBundledVarOrVar(v) or (isBundledVar(v) and v.multiExprType != key.multiExprType):
                        raise SpecializationFailure('May only relabel a Bundled Variable to Bundled Variables of the same type')
                # change ..x..:expression_or_expressions to x:expressions
                relabelVar = key.bundledExpr.variable
            else:
                raise SpecializationFailure("May only relabel a Variable or a Bundled Variable")   
            relabelMap[relabelVar] = sub
        # Process the substitution map, performming conversions of Operations and Etcetera-wrapped Operations/Variables
        substitutingVars = set()
        origSubMapItems = list(subMap.iteritems())
        subMap = dict()
        for subKey, sub in origSubMapItems:
            if isinstance(subKey, Variable):
                # substitute a simple Variable
                if not isinstance(sub, Expression) or isinstance(sub, Composite):
                    raise SpecializationFailure('A normal Variable may be not be specialized to a composite Expression (only a Bundled Variable may be)')
                subVar = subKey
                subMap[subVar] = sub
            elif isBundledVar(subKey):
                # substitute an Etcetera-wrapped Variable -- sub in an ExpressionList
                subVar = subKey.bundledExpr.variable
                sub = compositeExpression(sub)
                if sub.__class__ != subKey.multiExprType:
                    if subKey.multiExprType == ExpressionList:
                        raise SpecializationFailure('Etcetera Variables may only be specialized to a list of Expressions')
                    elif subKey.multiExprType == ExpressionTensor:
                        raise SpecializationFailure('Block Variables may only be specialized to a tensor of Expressions')
                    else:
                        raise SpecializationFailure('Unknown Bundle type:' + str(subKey.multiExprType))
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
                            raise SpecializationFailure('A normal operation may be not be specialized to a composite Expression (only a Bundled Operation may be)')                    
                        lambdaExpr = sub
                        subVar = operation.operator
                        subMap[subVar] = Lambda(operation.operands, lambdaExpr)
                    else: 
                        lambdaExpressions = compositeExpression(sub)
                        subVar = operation.operator.variable
                        subMap[subVar] = ExpressionList([Lambda(operation.operands, lambdaExpr) for lambdaExpr in lambdaExpressions])
                except TypeError as e:
                    raise SpecializationFailure("Improper Operation substitution, error transforming to Lambda: " + e.message)
                except ValueError as e:
                    raise SpecializationFailure("Improper Operation substitution, error transforming to Lambda: " + e.message)
            else:
                raise SpecializationFailure("Substitution may only map (Bundled) Variable types or (Bundled) Operations that have Variable operators")
            substitutingVars.add(subVar)
        if len(subMap) > 0:
            # an actual Forall specialization
            assert isinstance(generalExpr, Forall), 'May only perform substitution specialization on Forall Expressions (relabeling would be okay)'
            expr = generalExpr.operands
            lambdaExpr = expr['instance_mapping']
            domain = expr['domain'] if 'domain' in expr else None
            assert isinstance(lambdaExpr, Lambda), "Forall Operation bundledExpr must be a Lambda function, or a dictionary mapping 'lambda' to a Lambda function"
            # extract the instance expression and instance variables from the lambda expression        
            instanceVars, expr, conditions  = lambdaExpr.arguments, lambdaExpr.expression['instance_expression'], list(lambdaExpr.expression['conditions'])
            iVarSet = set().union(*[iVar.freeVars() for iVar in instanceVars])
            assert substitutingVars == iVarSet, 'The set of substituting variables must be that same as the set of Forall instance variables'
            for arg in lambdaExpr.arguments:
                if isinstance(arg, Variable) and arg in substitutingVars and isinstance(substitutingVars, ExpressionList):
                    raise SpecializationFailure("May only specialize a Forall instance variable with an ExpressionList if it is wrapped in Etcetera")
        else:
            # just a relabeling
            expr = generalExpr
            instanceVars = []
            conditions = []
            domain = None
        # make substitutions in the condition
        subbedConditions = [condition.substituted(subMap, relabelMap) for condition in conditions]
        # add conditions for satisfying the domain restriction if there is one
        if domain is not None:
            # extract all of the elements
            for var in instanceVars:
                elementOrList = var.substituted(subMap, relabelMap)
                for element in (elementOrList if isinstance(elementOrList, ExpressionList) else [elementOrList]):
                    subbedConditions.add(InSet(element, domain))
        return expr.substituted(subMap, relabelMap), subbedConditions, subMap, relabelMap

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
        for assumption in assumptions:
            if len(assumption.freeVars() & set(newForallVars)) != 0:
                raise GeneralizationFailure('Cannot generalize using assumptions that involve any of the new forall variables unless they are conditions of the generalization')
        instanceExpr = instanceTruth.expr
        generalizedExpr = Forall(instanceVars=newForallVars, instanceExpr=instanceExpr, domain=newDomain, conditions=newConditions)
        Generalization._checkGeneralization(generalizedExpr, instanceExpr)
        generalizedTruth = KnownTruth(generalizedExpr, assumptions, self)
        self.instanceTruth = instanceExpr
        Proof.__init__(self, generalizedTruth, [self.instanceTruth])

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

class ModusPonensFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class SpecializationFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class GeneralizationFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

    
    