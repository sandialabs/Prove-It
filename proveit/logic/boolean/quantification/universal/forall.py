from proveit import Literal, OperationOverInstances, USE_DEFAULTS, ExpressionList, Operation, Etcetera, MultiVariable
from proveit.common import P, Q, R, S

FORALL = Literal(__package__, stringFormat='forall', latexFormat=r'\forall')

class Forall(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpr, domain=None, conditions = tuple()):
        '''
        Create a Forall expression:
        forall_{instanceVars | conditions} instanceExpr.
        This expresses that the instanceExpr is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, FORALL, instanceVars, instanceExpr, domain, conditions)

    @classmethod
    def operatorOfOperation(subClass):
        return FORALL    
        
    def deriveSideEffects(self, knownTruth):
        '''
        Automatically unfold the Forall statement if the domain has an 'unfoldForall' method.
        '''
        if hasattr(self.domain, 'unfoldForall'):
            self.tryDerivation(self.unfold, knownTruth.assumptions)
        
    def conclude(self, assumptions):
        '''
        If the domain has a 'foldForall' method, attempt to conclude this Forall statement
        via 'concludeAsFolded'.
        '''
        if hasattr(self.domain, 'foldAsForall'):
            self.concludeAsFolded(assumptions)
        raise ProofFailure(self, assumptions, "Unable to conclude automatically; the domain has no 'foldAsForall' method.")

    def specialize(self, subMap=None, assumptions=USE_DEFAULTS, conditionAsHypothesis=False):
        '''
        From this Forall expression, and the condition if there is one,
        derive and return a specialized form.  If conditionAsHypothesis is True, 
        derive and return the implication with the condition as hypothesis 
        and specialized form as the conclusion.  Any instance variables
        excluded from subMap will default to themselves.  For items in
        subMap that do not pertain to instance variables, an attempt to
        relabel them will be made.
        '''
        from proveit._core_.proof import Specialization
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
        specialized = Specialization(self, subMap, relabelMap, assumptions).provenTruth
        if conditionAsHypothesis and self.hasCondition():
            return specialized.asImplication(self.conditions[0])
        return specialized
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From this forall statement, derive an "unfolded" version dependent upon the domain of the forall,
        calling unfoldForall on the condition.
        For example, from forall_{A in BOOLEANS} P(A), derives P(TRUE) and P(FALSE).
        '''    
        assert self.hasDomain(), "Cannot unfold a forall statement with no domain"
        assert len(self.instanceVars)==1, "Cannot unfold a forall statement with more than 1 instance variable (not implemented beyond this)"
        return self.domain.unfoldForall(self, assumptions)
    
    """
    def equateWithUnfolded(self):
        pass
    """
        
    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Conclude this forall statement from an "unfolded" version dependent upon the domain of the forall,
        calling foldAsForall on the condition.
        For example, conclude forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''    
        assert self.hasDomain(), "Cannot fold a forall statement with no domain"
        assert len(self.instanceVars)==1, "Cannot fold a forall statement with more than 1 instance variable (not implemented beyond this)"
        return self.domain.foldAsForall(self, assumptions)
    
    def deriveBundled(self, assumptions=USE_DEFAULTS):
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
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        R_op, R_op_sub = Etcetera(Operation(MultiVariable(R), innerForall.instanceVars)), innerForall.conditions
        return forallBundling.specialize({xEtc:self.instanceVars, yEtc:innerForall.instanceVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub, S:self.domain}).deriveConclusion(assumptions)

    def _specializeUnravelingTheorem(self, theorem, *instanceVarLists):
        from proveit.common import xEtc, yEtc
        assert len(self.instanceVars) > 1, "Can only unravel a forall statement with multiple instance variables"
        if len(instanceVarLists) == 1:
            raise ValueError("instanceVarLists should be a list of 2 or more Variable lists")
        if len(instanceVarLists) > 2:
            return self.deriveUnraveled(ExpressionList(instanceVarLists[:-1]), instanceVarLists[-1]).deriveUnraveled(*instanceVarLists[:-1]).checked({self})
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
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), outerVars)), outerConditions
        R_op, R_op_sub = Etcetera(Operation(MultiVariable(R), innerVars)), innerConditions
        return theorem.specialize({xEtc:outerVars, yEtc:innerVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub, S:self.domain}) 
           
    def deriveUnraveled(self, instanceVarLists, assumptions=USE_DEFAULTS):
        '''
        From a multi-variable forall statement, derive the nested, unravelled forall statement.  For example,
        forall_{x, y | Q(x), R(y)} P(x, y) becomes forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from theorems import forallUnraveling
        return self._specializeUnravelingTheorem(forallUnraveling, instanceVarLists).deriveConclusion(assumptions)
        
    def deriveUnraveledEquiv(self, instanceVarLists):
        '''
        From a multi-variable forall statement, derive its equivalence with a nested, unravelled forall statement.
        For example, forall_{x, y in DOMAIN | Q(x), R(y)} P(x, y) = forall_{x in DOMAIN | Q(x)} forall_{y in DOMAIN | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from theorems import forallBundledEquiv
        return self._specializeUnravelingTheorem(forallBundledEquiv, instanceVarLists)
        
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
            unravelledEquiv = self.deriveUnraveledEquiv(*[[var] for var in self.instanceVars]).checked()
            unravelledEval = unravelledEquiv.rhs.evaluate()
            return unravelledEquiv.applyTransitivity(unravelledEval).checked()            

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        as all forall expressions are (they are taken to be false when not true).
        '''
        from axioms import forallInBool
        from proveit.common import xEtc
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
        print forallInBool
        print xEtc, self.instanceVars        
        print P_op, P_op_sub
        print Q_op, Q_op_sub
        return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xEtc:self.instanceVars, S:self.domain})
