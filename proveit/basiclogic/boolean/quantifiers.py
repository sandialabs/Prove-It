from proveit.basiclogic.genericOps import OperationOverInstances
from proveit.expression import Expression, Literal, Operation, STRING, LATEX
from proveit.multiExpression import ExpressionList, Etcetera
from proveit.forallLiteral import FORALL
from proveit.everythingLiteral import EVERYTHING
from proveit.basiclogic.variables import P, Q, R, S, f, g, x, y

pkg = __package__

class Forall(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, conditions = tuple(), domain=EVERYTHING):
        '''
        Create a Forall expression:
        forall_{instanceVars | conditions} instanceExpr.
        This expresses that the instanceExpr is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, FORALL, instanceVars, instanceExpr, conditions, domain)
        
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
            return Implies(self.conditions[0], specialized).check({self})
        return specialized
    
    def equateMaps(self):
        '''
        From forall_{x | Q(x)} f(x) = g(x) derive and return 
        [x -> f(x) | Q(x)] = [x -> g(x) | Q(x)]
        '''
        from proveit.basiclogic.mapping.theorems import mapSubstitution, mapOverAllSubstitution
        from proveit.basiclogic import Equals
        assert isinstance(self.instanceExpr, Equals), "Instance expression must be an equality to use mapSubstitution"
        fOp, fOpSub = Operation(f, self.instanceVars), self.instanceExpr.lhs
        gOp, gOpSub = Operation(g, self.instanceVars), self.instanceExpr.rhs
        Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions
        if self.hasCondition():
            return mapSubstitution.specialize({fOp:fOpSub, gOp:gOpSub, Q_op:Q_op_sub, x:self.instanceVars, y:self.instanceVars}).deriveConclusion().check({self})
        else:
            return mapOverAllSubstitution.specialize({fOp:fOpSub, gOp:gOpSub}).deriveConclusion().check({self})
    
    def unfold(self):
        '''
        From this forall statement, derive an "unfolded" version dependent upon the domain of the forall,
        calling unfoldForall on the condition.
        For example, from forall_{A in BOOLEANS} P(A), derives P(TRUE) and P(FALSE).
        '''    
        assert self.hasDomain(), "Cannot unfold a forall statement with no domain"
        assert len(self.instanceVars)==1, "Cannot unfold a forall statement with more than 1 instance variable (not implemented beyond this)"
        return self.domain.unfoldForall(self)
    
    """
    def equateWithUnfolded(self):
        pass
    """
        
    def concludeAsFolded(self):
        '''
        Conclude this forall statement from an "unfolded" version dependent upon the domain of the forall,
        calling foldAsForall on the condition.
        For example, conclude forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''    
        assert self.hasDomain(), "Cannot fold a forall statement with no domain"
        assert len(self.instanceVars)==1, "Cannot fold a forall statement with more than 1 instance variable (not implemented beyond this)"
        return self.domain.foldAsForall(self)
    
    def deriveBundled(self):
        '''
        From a nested forall statement, derive the bundled forall statement.  For example,
        forall_{x | Q(x)} forall_{y | R(y)} P(x, y) becomes forall_{x, y | Q(x), R(y)} P(x, y).
        '''
        from theorems import forallBundling
        assert isinstance(self.instanceExpr, Forall), "Can only bundle nested forall statements"
        innerForall = self.instanceExpr
        composedInstanceVars = ExpressionList([self.instanceVars, innerForall.instanceVars])
        P_op, P_op_sub = Operation(P, composedInstanceVars), innerForall.instanceExpr
        multiQ_op, multiQ_op_sub = Operation(Q, self.instanceVars), self.conditions
        multiR_op, multiR_op_sub = Operation(R, innerForall.instanceVars), innerForall.conditions
        return forallBundling.specialize({x:self.instanceVars, y:innerForall.instanceVars, P_op:P_op_sub, multiQ_op:multiQ_op_sub, multiR_op:multiR_op_sub}).deriveConclusion().check({self})

    def _specializeUnravelingTheorem(self, theorem, *instanceVarLists):
        from proveit.basiclogic.simpleExpr import xEtc, yEtc
        assert len(self.instanceVars) > 1, "Can only unravel a forall statement with multiple instance variables"
        if len(instanceVarLists) == 1:
            raise ValueError("instanceVarLists should be a list of 2 or more Variable lists")
        if len(instanceVarLists) > 2:
            return self.deriveUnraveled(ExpressionList(instanceVarLists[:-1]), instanceVarLists[-1]).deriveUnraveled(*instanceVarLists[:-1]).check({self})
        outerVars, innerVars = instanceVarLists
        outerVarSet, innerVarSet = set(outerVars), set(innerVars)
        assert innerVarSet | outerVarSet == set(self.instanceVars), "outerVars and innterVars must combine to the full set of instance variables"
        assert innerVarSet.isdisjoint(outerVarSet), "outerVars and innterVars must be disjoint sets"
        innerConditions = []
        outerConditions = []
        for condition in self.conditions:
            if condition.freeVars().isdisjoint(innerVars):
                outerConditions.append(condition)
            else: innerConditions.append(condition)
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, outerVars)), outerConditions
        R_op, R_op_sub = Etcetera(Operation(R, innerVars)), innerConditions
        if self.domain is None:
            return theorem.specialize({xEtc:outerVars, yEtc:innerVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub}) 
        else:
            return theorem.specialize({xEtc:outerVars, yEtc:innerVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub, S:self.domain}) 
           
    def deriveUnraveled(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive the nested, unravelled forall statement.  For example,
        forall_{x, y | Q(x), R(y)} P(x, y) becomes forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from theorems import forallUnraveling
        return self._specializeUnravelingTheorem(forallUnraveling, *instanceVarLists).deriveConclusion().check({self})

    def deriveUnraveledEquiv(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive its equivalence with a nested, unravelled forall statement.
        For example, forall_{x, y in DOMAIN | Q(x), R(y)} P(x, y) = forall_{x in DOMAIN | Q(x)} forall_{y in DOMAIN | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from theorems import forallBundledEquiv
        return self._specializeUnravelingTheorem(forallBundledEquiv, *instanceVarLists).check()
        
    def evaluate(self):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's evaluateForall method
        '''
        from boolOps import _evaluate
        assert self.hasDomain(), "Cannot evaluate a forall statement with no domain"
        if len(self.instanceVars) == 1:
            # start with the first condition which may then nest over subsequent conditions
            return _evaluate(self, lambda : self.domain.evaluateForall(self))
        else:
            # Evaluate an unravelled version
            unravelledEquiv = self.deriveUnraveledEquiv(*[[var] for var in self.instanceVars]).check()
            unravelledEval = unravelledEquiv.rhs.evaluate()
            return unravelledEquiv.applyTransitivity(unravelledEval).check()            

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        as all forall expressions are (they are taken to be false when not true).
        '''
        from axioms import forallInBool
        from proveit.basiclogic.simpleExpr import xEtc
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        print forallInBool
        print xEtc, self.instanceVars        
        print P_op, P_op_sub
        print Q_op, Q_op_sub
        return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).check()

# The FORALL Literal is defined at the top level of prove-it, but its operationMaker must be set here.
FORALL.formatMap = {STRING:'forall', LATEX:r'\forall'}
def forallMaker(operands=None, instanceVars=None, instanceExpr=None, conditions=None, domain=EVERYTHING):
    if operands is not None:
        return Forall(*OperationOverInstances.extractParameters(operands))
    else:
        return Forall(instanceVars, instanceExpr, conditions, domain)
FORALL.operationMaker = forallMaker

class Exists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, conditions=tuple(), domain=EVERYTHING):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVars | condition} instanceExpr
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpr is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, EXISTS, instanceVars, instanceExpr, conditions, domain)

    def concludeViaExample(self, exampleInstance):
        '''
        Conclude and return this [exists_{y | Q(x)} P(y)] from P(x) and Q(x), where x is the given exampleInstance.
        '''
        from theorems import existenceByExample
        # P(x) where x is the given exampleInstance
        exampleExpr = self.instanceExpr.substituted({self.instanceVars:exampleInstance})
        # Q(x) where x is the given exampleInstance
        exampleConditions = self.conditions.substituted({self.instanceVars:exampleInstance})
        # forall_{P, Q} forall_{x | Q(x)} [P(x) => exists_{y | Q(x)} P(y)]
        return existenceByExample.specialize({Operation(P, self.instanceVars): self.instanceExpr, Operation(Q, self.instanceVars): self.conditions, y:self.instanceVars}).specialize({x:exampleInstance}).deriveConclusion().check({exampleExpr, exampleConditions})

    def deriveNegatedForall(self):
        '''
        From [exists_{x | Q(x)} Not(P(x))], derive and return Not(forall_{x | Q(x)} P(x)).
        From [exists_{x | Q(x)} P(x)], derive and return Not(forall_{x | Q(x)} (P(x) != TRUE)).
        '''
        from axioms import existsDef
        from theorems import existsNotImpliesNotForall
        from boolOps import Not
        Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions
        if isinstance(self.instanceExpr, Not):
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr.operands
            return existsNotImpliesNotForall.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).deriveConclusion().check({self})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
            return existsDef.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).deriveRightViaEquivalence().check({self})
    
    def deduceInBool(self):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        from theorems import existsInBool
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions
        return existsInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).check()

EXISTS = Literal(pkg, 'EXISTS', {STRING:'exists', LATEX:r'\exists'}, lambda operands : Exists(*OperationOverInstances.extractParameters(operands)))

class NotExists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, conditions=tuple(), domain=EVERYTHING):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVars | conditions} instanceExpr
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpr is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, NOTEXISTS, instanceVars, instanceExpr, conditions, domain)
        
    def unfold(self):
        '''
        Deduce and return Not(Exists_{x | Q(x)} P(x)) from NotExists_{x | Q(x)} P(x)
        '''
        from theorems import notExistsUnfolding
        Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        return notExistsUnfolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).deriveConclusion().check({self})
    
    def concludeAsFolded(self):
        '''
        Prove and return some NotExists_{x | Q(x)} P(x) assuming Not(Exists_{x | Q(x)} P(x)).
        '''
        from theorems import notExistsFolding
        Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        folding = notExistsFolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars})
        return folding.deriveConclusion().check({self.unfold()})

    """
    # MUST BE UPDATED
    def concludeViaForall(self):
        '''
        Prove and return either some NotExists_{x | Q(x)} Not(P(x)) or NotExists_{x | Q(x)} P(x)
        assuming forall_{x | Q(x)} P(x) or assuming forall_{x | Q(x)} (P(x) != TRUE) respectively.
        '''
        from theorems import forallImpliesNotExistsNot, existsDefNegation
        from proveit.basiclogic.equality.eqOps import NotEquals
        from boolOps import Not
        from boolSet import TRUE
        Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions
        operand = self.operans[0]
        if isinstance(self.instanceExpr, Not):
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr.etcExpr
            assumption = Forall(operand.arguments, operand.expression.etcExpr, operand.domainCondition)
            return forallImpliesNotExistsNot.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).deriveConclusion().check({assumption})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
            assumption = Forall(operand.arguments, NotEquals(operand.expression, TRUE), operand.domainCondition)
            return existsDefNegation.specialize({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instanceVars}).deriveLeftViaEquivalence().check({assumption})
    """


NOTEXISTS = Literal(pkg, 'NOTEXISTS', {STRING:'notexists', LATEX:r'\nexists'}, lambda operands : NotExists(*OperationOverInstances.extractParameters(operands)))
