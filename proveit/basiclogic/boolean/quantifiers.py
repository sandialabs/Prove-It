from proveit.basiclogic.genericOperations import OperationOverInstances
from proveit.expression import Expression, Literal, Operation, STRING, LATEX
from proveit.multiExpression import ExpressionList
from proveit.forallLiteral import FORALL
from proveit.basiclogic.variables import P, Q, R, f, g, x, y

pkg = __package__

class Forall(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions = None):
        '''
        Create a Forall expression:
        forall_{instanceVar | condition} instanceExpression.
        This expresses that the instanceExpression is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, FORALL, instanceVars, instanceExpression, conditions)
        
    def specialize(self, subMap=None, conditionAsHypothesis=False):
        '''
        From this Forall expression, and the condition if there is one,
        derive and return a specialized form.  If conditionAsHypothesis is True, 
        derive and return the implication with the condition as hypothesis 
        and specialized form as the conclusion.
        '''
        from boolOps import Implies
        specialized = Expression.specialize(self, subMap)
        if conditionAsHypothesis and self.hasCondition():
            return Implies(self.condition, specialized).check({self})
        return specialized
    
    def equateMaps(self):
        '''
        From forall_{x | Q(x)} f(x) = g(x) derive and return 
        [x -> f(x) | Q(x)] = [x -> g(x) | Q(x)]
        '''
        from proveit.basiclogic.mapping.theorems import mapSubstitution, mapOverAllSubstitution
        from proveit.basiclogic import Equals
        assert isinstance(self.instanceExpression, Equals), "Instance expression must be an equality to use mapSubstitution"
        fOp, fOpSub = Operation(f, self.instanceVar), self.instanceExpression.lhs
        gOp, gOpSub = Operation(g, self.instanceVar), self.instanceExpression.rhs
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        if self.hasCondition():
            return mapSubstitution.specialize({fOp:fOpSub, gOp:gOpSub, Q_op:Q_op_sub, x:self.instanceVar, y:self.instanceVar}).deriveConclusion().check({self})
        else:
            return mapOverAllSubstitution.specialize({fOp:fOpSub, gOp:gOpSub}).deriveConclusion().check({self})
    
    def unfold(self):
        '''
        From this forall statement, derive an "unfolded" version dependent upon the condition of the forall,
        calling unfoldForall on the condition.
        For example, from forall_{A in BOOLEANS} P(A), derives P(TRUE) and P(FALSE).
        '''    
        return self.condition.unfoldForall(self)
    
    def equateWithUnfolded(self):
        pass
        
    def concludeAsFolded(self):
        '''
        Conclude this forall statement from an "unfolded" version dependent upon the condition of the forall,
        calling foldAsForall on the condition.
        For example, conclude forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''    
        return self.condition.foldAsForall(self)
    
    def deriveBundled(self):
        '''
        From a nested forall statement, derive the bundled forall statement.  For example,
        forall_{x | Q(x)} forall_{y | R(y)} P(x, y) becomes forall_{x, y | Q(x), R(y)} P(x, y).
        '''
        from theorems import forallBundling
        assert isinstance(self.instanceExpression, Forall), "Can only bundle nested forall statements"
        innerForall = self.instanceExpression
        composedInstanceVars = ExpressionList([self.instanceVar, innerForall.instanceVar])
        P_op, P_op_sub = Operation(P, composedInstanceVars), innerForall.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(Q, self.instanceVar), self.condition
        multiR_op, multiR_op_sub = Operation(R, innerForall.instanceVar), innerForall.condition
        return forallBundling.specialize({x:self.instanceVar, y:innerForall.instanceVar, P_op:P_op_sub, multiQ_op:multiQ_op_sub, multiR_op:multiR_op_sub}).deriveConclusion().check({self})

    def _specializeUnravellingTheorem(self, theorem, *instanceVarLists):
        print instanceVarLists
        assert len(self.instanceVar) > 1, "Can only unravel a forall statement with multiple instance variables"
        if len(instanceVarLists) == 1:
            raise ValueError("instanceVarLists should be a list of 2 or more Variable lists")
        if len(instanceVarLists) > 2:
            return self.deriveUnravelled(ExpressionList(instanceVarLists[:-1]), instanceVarLists[-1]).deriveUnravelled(*instanceVarLists[:-1]).check({self})
        outerVars, innerVars = instanceVarLists
        outerVarSet, innerVarSet = set(outerVars), set(innerVars)
        assert innerVarSet | outerVarSet == set(self.instanceVar), "outerVars and innterVars must combine to the full set of instance variables"
        assert innerVarSet.isdisjoint(outerVarSet), "outerVars and innterVars must be disjoint sets"
        innerConditions = []
        outerConditions = []
        for condition in self.condition:
            if condition.freeVars().isdisjoint(innerVars):
                outerConditions.append(condition)
            else: innerConditions.append(condition)
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        Q_op, Q_op_sub = Operation(Q, outerVars), outerConditions
        R_op, R_op_sub = Operation(R, innerVars), innerConditions
        return theorem.specialize({x:outerVars, y:innerVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub}) 
           
    def deriveUnravelled(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive the nested, unravelled forall statement.  For example,
        forall_{x, y | Q(x), R(y)} P(x, y) becomes forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from theorems import forallUnravelling
        return self._specializeUnravellingTheorem(forallUnravelling, *instanceVarLists).deriveConclusion().check({self})

    def deriveUnravelledEquiv(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive its equivalence with a nested, unravelled forall statement.
        For example, forall_{x, y | Q(x), R(y)} P(x, y) = forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from theorems import forallBundledEquiv
        return self._specializeUnravellingTheorem(forallBundledEquiv, *instanceVarLists).check()
        
    def evaluate(self):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's evaluateForall method
        '''
        from boolOps import _evaluate
        assert self.hasCondition(), "Cannot evaluate a forall statement with no conditions"
        if len(self.instanceVar) == 1:
            # start with the first condition which may then nest over subsequent conditions
            return _evaluate(self, lambda : self.condition.evaluateForall(self))
        else:
            # Evaluate an unravelled version
            unravelledEquiv = self.deriveUnravelledEquiv(*[condition.freeVars() for condition in self.condition]).check()
            unravelledEval = unravelledEquiv.rhs.evaluate()
            return unravelledEquiv.applyTransitivity(unravelledEval).check()            

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        as all forall expressions are (they are taken to be false when not true).
        '''
        from axioms import forallInBool
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar}).check()

# The FORALL Literal is defined at the top level of prove-it, but its operationMaker must be set here.
FORALL.formatMap = {STRING:'forall', LATEX:r'\forall'}
FORALL.operationMaker = lambda operand : Forall(operand.argument, operand.expression, operand.domainCondition)

class Exists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVar | condition} instanceExpression
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpression is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, EXISTS, instanceVars, instanceExpression, conditions)

    def concludeViaExample(self, exampleInstance):
        '''
        Conclude and return this [exists_{y | Q(x)} P(y)] from P(x) and Q(x), where x is the given exampleInstance.
        '''
        from theorems import existenceByExample
        # P(x) where x is the given exampleInstance
        exampleExpr = self.instanceExpression.substituted({self.instanceVar:exampleInstance})
        # Q(x) where x is the given exampleInstance
        exampleCondition = self.condition.substituted({self.instanceVar:exampleInstance})
        # forall_{P, Q} forall_{x | Q(x)} [P(x) => exists_{y | Q(x)} P(y)]
        return existenceByExample.specialize({Operation(P, self.instanceVar): self.instanceExpression, Operation(Q, self.instanceVar): self.condition, y:self.instanceVar}).specialize({x:exampleInstance}).deriveConclusion().check({exampleExpr, exampleCondition})

    def deriveNegatedForall(self):
        '''
        From [exists_{x** | Q**(x**)} Not(P(x**))], derive and return Not(forall_{x** | Q**(x**)} P(x**)).
        From [exists_{x** | Q**(x**)} P(x**)], derive and return Not(forall_{x** | Q**(x**)} (P(x**) != TRUE)).
        '''
        from axioms import existsDef
        from theorems import existsNotImpliesNotForall
        from boolOps import Not
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        if isinstance(self.instanceExpression, Not):
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression.operand
            return existsNotImpliesNotForall.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar}).deriveConclusion().check({self})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
            return existsDef.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar}).deriveRightViaEquivalence().check({self})
    
    def deduceInBool(self):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        from theorems import existsInBool
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        return existsInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar}).check()

EXISTS = Literal(pkg, 'EXISTS', {STRING:'exists', LATEX:r'\exists'}, lambda operand : Exists(operand.argument, operand.expression, operand.domainCondition))

class NotExists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVar | condition} instanceExpression
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpression is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, NOTEXISTS, instanceVars, instanceExpression, conditions)
        
    def unfold(self):
        '''
        Deduce and return Not(Exists_{x** | Q**(x**)} P(x**)) from NotExists_{x** | Q**(x**)} P(x**)
        '''
        from theorems import notExistsUnfolding
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        return notExistsUnfolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar}).deriveConclusion().check({self})
    
    def concludeAsFolded(self):
        '''
        Prove and return some NotExists_{x** | Q**(x**)} P(x**) assuming Not(Exists_{x** | Q**(x**)} P(x**)).
        '''
        from theorems import notExistsFolding
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        folding = notExistsFolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar})
        return folding.deriveConclusion().check({self.unfold()})
    
    def concludeViaForall(self):
        '''
        Prove and return either some NotExists_{x** | Q**(x**)} Not(P(x**)) or NotExists_{x** | Q**(x**)} P(x**)
        assumint forall_{x** | Q**(x**)} P(x**) or assuming forall_{x** | Q**(x**)} (P(x) != TRUE) respectively.
        '''
        from theorems import forallImpliesNotExistsNot, existsDefNegation
        from proveit.basiclogic.equality.eqOps import NotEquals
        from boolOps import Not
        from boolSet import TRUE
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        operand = self.operand
        if isinstance(self.instanceExpression, Not):
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression.operand
            assumption = Forall(operand.argument, operand.expression.operand, operand.domainCondition)
            return forallImpliesNotExistsNot.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar}).deriveConclusion().check({assumption})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
            assumption = Forall(operand.argument, NotEquals(operand.expression, TRUE), operand.domainCondition)
            return existsDefNegation.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVar}).deriveLeftViaEquivalence().check({assumption})

NOTEXISTS = Literal(pkg, 'NOTEXISTS', {STRING:'notexists', LATEX:r'\nexists'}, lambda operand : NotExists(operand.argument, operand.expression, operand.domainCondition))
