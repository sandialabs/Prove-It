from proveit import Expression, Literal, OperationOverInstances, defaults, USE_DEFAULTS, ExprTuple, Operation, ProofFailure
from proveit._common_ import P, Q, R, S, xx, yy, QQ, RR
from proveit._core_.proof import Generalization

class Forall(OperationOverInstances):
    # operator of the Forall operation
    _operator_ = Literal(stringFormat='forall', latexFormat=r'\forall', context=__file__)
    
    def __init__(self, instanceParamOrParams, instanceExpr, domain=None, domains=None, 
                 conditions = tuple(), _lambda_map=None):
        '''
        Create a Forall expression:
        forall_{instanceParamOrParams | conditions} instanceExpr.
        This expresses that the instanceExpr is true for all values of the 
        instance parameter(s) given that the optional condition(s) is/are 
        satisfied.  The instance parameter(s) and condition(s)
        may be singular or plural (iterable).
        '''
        # nestMultiIvars=True will cause it to treat multiple instance 
        # variables as nested Forall operations internally
        # and only join them together as a style consequence.
        OperationOverInstances.__init__(self, Forall._operator_, instanceParamOrParams, 
                                        instanceExpr, domain, domains, conditions, 
                                        nestMultiIvars=True, _lambda_map=_lambda_map)
        
    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for this forall operation.
        '''
        if self.hasDomain() and hasattr(self.domain, 'unfoldForall'):
            if len(self.conditions)==0:
                yield self.unfold # derive an unfolded version (dependent upon the domain)
        
    def conclude(self, assumptions):
        '''
        If the instance expression, or some instance expression of 
        nested universal quantifiers, is known to be true, conclude
        via generalization.  Otherwise, if the domain has a 'foldForall'
        method, attempt to conclude this Forall statement
        via 'concludeAsFolded'.
        '''
        # first try to prove via generalization without automation
        assumptions = defaults.checkedAssumptions(assumptions)
        expr = self
        instanceParamLists = []
        conditions = []
        while isinstance(expr, Forall):
            new_params = expr.explicitInstanceParams()
            instanceParamLists.append(list(new_params))
            conditions += list(expr.inclusiveConditions())
            expr = expr.explicitInstanceExpr()
            new_assumptions = assumptions + tuple(conditions)
            if expr.proven(assumptions=assumptions + tuple(conditions)):
                proven_inst_expr = expr.prove(new_assumptions)
                return proven_inst_expr.generalize(instanceParamLists, 
                                                   conditions=conditions)
        # next try 'foldAsForall' on the domain (if applicable)
        if self.hasDomain() and hasattr(self.domain, 'foldAsForall'):
            # try foldAsForall first
            try:
                return self.concludeAsFolded(assumptions)
            except:
                raise ProofFailure(self, assumptions, 
                                   "Unable to conclude automatically; "
                                   "the 'foldAsForall' method on the "
                                   "domain failed.")
        raise ProofFailure(self, assumptions, 
                           "Unable to conclude automatically; a "
                           "universally quantified instance expression "
                           "is not known to be true and the domain has "
                           "no 'foldAsForall' method.")
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From this forall statement, derive an "unfolded" version dependent upon the domain of the forall,
        calling unfoldForall on the condition.
        For example, from forall_{A in BOOLEANS} P(A), derives P(TRUE) and P(FALSE).
        '''    
        assert self.hasDomain(), "Cannot unfold a forall statement with no domain"
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
        from proveit import KnownTruth
        assert self.hasDomain(), "Cannot fold a forall statement with no domain"
        #assert len(self.instanceVars)==1, "Cannot fold a forall statement with more than 1 instance variable (not implemented beyond this)"
        #expr = self.unraveled()
        return self.domain.foldAsForall(self, assumptions)
        #print(truth)
        #return truth.generalize(self.instanceVar, conditions=self.conditions)
    
    def deriveBundled(self, assumptions=USE_DEFAULTS):
        '''
        From a nested forall statement, derive the bundled forall statement.  For example,
        forall_{x | Q(x)} forall_{y | R(y)} P(x, y) becomes forall_{x, y | Q(x), R(y)} P(x, y).
        '''
        raise NotImplementedError("Need to update")
        from ._theorems_ import bundling
        assert isinstance(self.instanceExpr, Forall), "Can only bundle nested forall statements"
        innerForall = self.instanceExpr
        composedInstanceVars = ExprTuple([self.instanceVars, innerForall.instanceVars])
        P_op, P_op_sub = Operation(P, composedInstanceVars), innerForall.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        R_op, R_op_sub = Operation(Rmulti, innerForall.instanceVars), innerForall.conditions
        return bundling.specialize({xMulti:self.instanceVars, yMulti:innerForall.instanceVars, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub, S:self.domain}).deriveConclusion(assumptions)

    def instantiate(self, repl_map=None, assumptions=USE_DEFAULTS):
        '''
        First attempt to prove that this Forall statement is true under the 
        assumptions, and then call specialize on the KnownTruth.
        '''
        return self.prove(assumptions).instantiate(repl_map, assumptions=assumptions)

    def specialize(self, repl_map=None, assumptions=USE_DEFAULTS):
        '''
        TEMPORARY FOR BACKWARD COMPATIBILITY
        '''
        return self.prove(assumptions).instantiate(repl_map, assumptions=assumptions)    
        
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's forallEvaluation method
        '''
        assert self.hasDomain(), "Cannot automatically evaluate a forall statement with no domain"

        if len(list(self.instanceParamLists())) == 1:
            # Use the domain's forallEvaluation method
            return self.domain.forallEvaluation(self, assumptions)
        else:
            # Evaluate an unravelled version
            unravelledEquiv = self.deriveUnraveledEquiv([var for var in (list(self.instanceVarLists()))])
            return unravelledEquiv.rhs.evaluation(assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        as all forall expressions are (they are taken to be false when not true).
        '''
        raise NotImplementedError("Need to update")
        from ._axioms_ import forallInBool
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xMulti:self.instanceVars, S:self.domain})
