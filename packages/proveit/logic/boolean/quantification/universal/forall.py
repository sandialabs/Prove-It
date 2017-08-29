from proveit import Literal, OperationOverInstances, USE_DEFAULTS, ExpressionList, Operation, ProofFailure
from proveit._common_ import P, Q, R, S, xMulti, yMulti, Qmulti, Rmulti

class Forall(OperationOverInstances):
    # operator of the Forall operation
    _operator_ = Literal(stringFormat='forall', latexFormat=r'\forall', context=__file__)
    
    def __init__(self, instanceVars, instanceExpr, domain=None, conditions = tuple()):
        '''
        Create a Forall expression:
        forall_{instanceVars | conditions} instanceExpr.
        This expresses that the instanceExpr is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, Forall._operator_, instanceVars, instanceExpr, domain, conditions)
        
    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for this forall operation.
        '''
        if hasattr(self.domain, 'unfoldForall'):
            yield self.unfold # derive an unfolded version (dependent upon the domain)
        
    def conclude(self, assumptions):
        '''
        If the domain has a 'foldForall' method, attempt to conclude this Forall statement
        via 'concludeAsFolded'.
        '''
        if hasattr(self.domain, 'foldAsForall'):
            return self.concludeAsFolded(assumptions)
        raise ProofFailure(self, assumptions, "Unable to conclude automatically; the domain has no 'foldAsForall' method.")
    
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
        from _theorems_ import forallBundling
        assert isinstance(self.instanceExpr, Forall), "Can only bundle nested forall statements"
        innerForall = self.instanceExpr
        composedInstanceVars = ExpressionList([self.instanceVars, innerForall.instanceVars])
        P_op, P_op_sub = Operation(P, composedInstanceVars), innerForall.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        R_op, R_op_sub = Operation(Rmulti, innerForall.instanceVars), innerForall.conditions
        return forallBundling.specialize({xMulti:self.instanceVars, yMulti:innerForall.instanceVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub, S:self.domain}).deriveConclusion(assumptions)

    def specialize(self, specializeMap=None, relabelMap=None, assumptions=USE_DEFAULTS):
        '''
        First attempt to prove that this Forall statement is true under the assumptions,
        and then call specialize on the KnownTruth.
        '''
        return self.prove(assumptions).specialize(specializeMap, relabelMap, assumptions=assumptions)

    def _specializeUnravelingTheorem(self, theorem, *instanceVarLists):
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
        Q_op, Q_op_sub = Operation(Qmulti, outerVars), outerConditions
        R_op, R_op_sub = Operation(Rmulti, innerVars), innerConditions
        return theorem.specialize({xMulti:outerVars, yMulti:innerVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub, S:self.domain}) 
           
    def deriveUnraveled(self, instanceVarLists, assumptions=USE_DEFAULTS):
        '''
        From a multi-variable forall statement, derive the nested, unravelled forall statement.  For example,
        forall_{x, y | Q(x), R(y)} P(x, y) becomes forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from _theorems_ import forallUnraveling
        return self._specializeUnravelingTheorem(forallUnraveling, instanceVarLists).deriveConclusion(assumptions)
        
    def deriveUnraveledEquiv(self, instanceVarLists):
        '''
        From a multi-variable forall statement, derive its equivalence with a nested, unravelled forall statement.
        For example, forall_{x, y in DOMAIN | Q(x), R(y)} P(x, y) = forall_{x in DOMAIN | Q(x)} forall_{y in DOMAIN | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        from _theorems_ import forallBundledEquiv
        return self._specializeUnravelingTheorem(forallBundledEquiv, instanceVarLists)
        
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's evaluateForall method
        '''
        assert self.hasDomain(), "Cannot automatically evaluate a forall statement with no domain"
        if len(self.instanceVars) == 1:
            # Use the domain's evaluateForall method
            return self.domain.evaluateForall(self, assumptions)
        else:
            # Evaluate an unravelled version
            unravelledEquiv = self.deriveUnraveledEquiv(*[[var] for var in self.instanceVars])
            return unravelledEquiv.rhs.evaluate(assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        as all forall expressions are (they are taken to be false when not true).
        '''
        from _axioms_ import forallInBool
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xMulti:self.instanceVars, S:self.domain})
