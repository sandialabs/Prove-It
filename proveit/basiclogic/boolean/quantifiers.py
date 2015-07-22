from proveit.basiclogic.genericOps import OperationOverInstances
from proveit.expression import Expression, Literal, Operation, STRING, LATEX
from proveit.multiExpression import ExpressionList, Etcetera
from proveit.forallLiteral import FORALL
from proveit.everythingLiteral import EVERYTHING
from proveit.common import P, Q, R, S

pkg = __package__

class Forall(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, domain=EVERYTHING, conditions = tuple()):
        '''
        Create a Forall expression:
        forall_{instanceVars | conditions} instanceExpr.
        This expresses that the instanceExpr is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, FORALL, instanceVars, instanceExpr, domain, conditions)
        
    def specialize(self, subMap=None, conditionAsHypothesis=False):
        '''
        From this Forall expression, and the condition if there is one,
        derive and return a specialized form.  If conditionAsHypothesis is True, 
        derive and return the implication with the condition as hypothesis 
        and specialized form as the conclusion.  Any instance variables
        excluded from subMap will default to themselves.  For items in
        subMap that do not pertain to instance variables, an attempt to
        relabel them will be made.
        '''
        from boolOps import Implies
        # Note that we use freeVars to deal with Etcetera-wrapped Variables
        iVarSet = set().union(*[iVar.freeVars() for iVar in self.instanceVars])
        explicitlySubbed = set()
        if subMap is None: subMap = dict()
        # move subMap items into relabelMap for non-instance variables
        origSubMapItems = list(subMap.iteritems())
        subMap, relabelMap = dict(), dict()
        subVars = set()
        for key, val in origSubMapItems:
            keyVars = key.freeVars()
            subVars.update(keyVars)
            if iVarSet.isdisjoint(keyVars):
                relabelMap[key] = val
            else:
                subMap[key] = val
                explicitlySubbed.update(keyVars)
        # default instance variables to themselves
        for var in iVarSet:
            if var not in subVars: subMap[var] = var 
        specialized = Expression.specialize(self, subMap, relabelMap)
        if conditionAsHypothesis and self.hasCondition():
            return Implies(self.conditions[0], specialized).check({self})
        return specialized
    
    """
    # out of data
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
    """
    
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
        from proveit.common import xEtc, yEtc
        assert isinstance(self.instanceExpr, Forall), "Can only bundle nested forall statements"
        innerForall = self.instanceExpr
        composedInstanceVars = ExpressionList([self.instanceVars, innerForall.instanceVars])
        P_op, P_op_sub = Operation(P, composedInstanceVars), innerForall.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        R_op, R_op_sub = Etcetera(Operation(R, innerForall.instanceVars)), innerForall.conditions
        return forallBundling.specialize({xEtc:self.instanceVars, yEtc:innerForall.instanceVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub, S:self.domain}).deriveConclusion().check({self})

    def _specializeUnravelingTheorem(self, theorem, *instanceVarLists):
        from proveit.common import xEtc, yEtc
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
        from proveit.common import xEtc
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        print forallInBool
        print xEtc, self.instanceVars        
        print P_op, P_op_sub
        print Q_op, Q_op_sub
        return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).check()

# The FORALL Literal is defined at the top level of prove-it, but its operationMaker must be set here.
FORALL.formatMap = {STRING:'forall', LATEX:r'\forall'}
def forallMaker(operands=None, instanceVars=None, instanceExpr=None, domain=EVERYTHING, conditions=None):
    if operands is not None:
        params = OperationOverInstances.extractParameters(operands)
        return Forall(params['instanceVars'], params['instanceExpr'], params['domain'], params['conditions'])
    else:
        return Forall(instanceVars, instanceExpr, domain, conditions)
FORALL.operationMaker = forallMaker

class Exists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, domain=EVERYTHING, conditions=tuple()):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVars | condition} instanceExpr
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpr is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, EXISTS, instanceVars, instanceExpr, domain, conditions)

    def concludeViaExample(self, exampleInstance):
        '''
        Conclude and return this [exists_{..y.. in S | ..Q(..x..)..} P(..y..)] from P(..x..) and Q(..x..) and ..x.. in S, where ..x.. is the given exampleInstance.
        '''
        from theorems import existenceByExample
        from proveit.basiclogic import In
        from proveit.common import xEtc, yEtc
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        # P(..x..) where ..x.. is the given exampleInstance
        exampleExpr = self.instanceExpr.substituted({self.instanceVars:exampleInstance})
        # ..Q(..x..).. where ..x.. is the given exampleInstance
        exampleConditions = self.conditions.substituted({self.instanceVars:exampleInstance})
        if self.domain != EVERYTHING:
            for iVar in self.instanceVars:
                exampleConditions.append(In(iVar, self.domain))
        # exists_{..y.. | ..Q(..x..)..} P(..y..)]
        return existenceByExample.specialize({P_op:P_op_sub, Q_op:Q_op_sub, yEtc:self.instanceVars, S:self.domain}).specialize({xEtc:exampleInstance}).deriveConclusion().check({exampleExpr, exampleConditions})

    def deriveNegatedForall(self):
        '''
        From [exists_{x | Q(x)} Not(P(x))], derive and return Not(forall_{x | Q(x)} P(x)).
        From [exists_{x | Q(x)} P(x)], derive and return Not(forall_{x | Q(x)} (P(x) != TRUE)).
        '''
        from axioms import existsDef
        from theorems import existsNotImpliesNotForall
        from boolOps import Not
        from proveit.common import xEtc        
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        if isinstance(self.instanceExpr, Not):
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr.operand
            return existsNotImpliesNotForall.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).deriveConclusion().check({self})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
            return existsDef.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).deriveRightViaEquivalence().check({self})
    
    def deduceInBool(self):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        from theorems import existsInBool
        from proveit.common import xEtc        
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        return existsInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).check()

def existsMaker(operands):
    params = OperationOverInstances.extractParameters(operands)
    return Exists(params['instanceVars'], params['instanceExpr'], params['domain'], params['conditions'])
EXISTS = Literal(pkg, 'EXISTS', {STRING:'exists', LATEX:r'\exists'}, existsMaker)

class NotExists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, domain=EVERYTHING, conditions=tuple()):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVars | conditions} instanceExpr
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpr is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, NOTEXISTS, instanceVars, instanceExpr, domain, conditions)
        
    def unfold(self):
        '''
        Deduce and return Not(Exists_{x | Q(x)} P(x)) from NotExists_{x | Q(x)} P(x)
        '''
        from theorems import notExistsUnfolding
        from proveit.common import xEtc
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        return notExistsUnfolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain}).deriveConclusion().check({self})
    
    def concludeAsFolded(self):
        '''
        Prove and return some NotExists_{x | Q(x)} P(x) assuming Not(Exists_{x | Q(x)} P(x)).
        '''
        from theorems import notExistsFolding
        from proveit.common import xEtc
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(Q, self.instanceVars)), self.conditions
        folding = notExistsFolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain})
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

def notExistsMaker(operands):
    params = OperationOverInstances.extractParameters(operands)
    return NotExists(params['instanceVars'], params['instanceExpr'], params['domain'], params['conditions'])
NOTEXISTS = Literal(pkg, 'NOTEXISTS', {STRING:'notexists', LATEX:r'\nexists'}, notExistsMaker)
