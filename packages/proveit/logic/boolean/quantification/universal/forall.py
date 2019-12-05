from proveit import Expression, Literal, OperationOverInstances, defaults, USE_DEFAULTS, ExprTuple, Operation, ProofFailure
from proveit._common_ import P, Q, R, S, xx, yy, QQ, RR
from proveit._core_.proof import Generalization

class Forall(OperationOverInstances):
    # operator of the Forall operation
    _operator_ = Literal(stringFormat='forall', latexFormat=r'\forall', context=__file__)

    def __init__(self, instanceVarOrVars, instanceExpr, domain=None, domains=None,
                 conditions = tuple(), _lambda_map=None):
        '''
        Create a Forall expression:
        forall_{instanceVars | conditions} instanceExpr.
        This expresses that the instanceExpr is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        # nestMultiIvars=True will cause it to treat multiple instance
        # variables as nested Forall operations internally
        # and only join them together as a style consequence.
        OperationOverInstances.__init__(self, Forall._operator_, instanceVarOrVars,
                                        instanceExpr, domain, domains, conditions,
                                        nestMultiIvars=True, _lambda_map=_lambda_map)

    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for this forall operation.
        '''
        if self.hasDomain() and hasattr(self.domain, 'unfoldForall'):
            yield self.unfold # derive an unfolded version (dependent upon the domain)

    def conclude(self, assumptions):
        '''
        If the domain has a 'foldForall' method, attempt to conclude this Forall statement
        via 'concludeAsFolded' or by proving the instance expression under proper assumptions
        and then generalizing.
        '''
        # first try to prove via generalization without automation
        extra_assumptions = tuple(self.inclusiveConditions())
        try:
            proven_inst_expr = self.explicitInstanceExpr().prove(assumptions=extra_assumptions+defaults.checkedAssumptions(assumptions), automation=False)
            return proven_inst_expr.generalize(self.explicitInstanceVars(), conditions=extra_assumptions)
        except:
            pass
        # next try 'foldAsForall' on the domain (if applicable)
        hasFoldAsForall=False
        if self.hasDomain() and hasattr(self.domain, 'foldAsForall'):
            # try foldAsForall first
            hasFoldAsForall=True
            try:
                return self.concludeAsFolded(assumptions)
            except:
                pass
        # lastly, try to prove via generalization with automation
        try:
            proven_inst_expr = self.explicitInstanceExpr().prove(assumptions=extra_assumptions+defaults.checkedAssumptions(assumptions))
            instanceVarLists = [list(self.explicitInstanceVars())]
            conditions = list(self.inclusiveConditions())
            # see if we can generalize multiple levels simultaneously for a shorter proof
            while isinstance(proven_inst_expr.proof(), Generalization):
                instanceVarLists.append(list(proven_inst_expr.explicitInstanceVars()))
                conditions += proven_inst_expr.conditions
                proven_inst_expr = proven_inst_expr.proof().requiredTruths[0]
            return proven_inst_expr.generalize(forallVarLists=instanceVarLists, conditions=conditions)
        except ProofFailure:
            if hasFoldAsForall:
                raise ProofFailure(self, assumptions, "Unable to conclude automatically; both the 'foldAsForall' method on the domain and automated generalization failed.")
            else:
                raise ProofFailure(self, assumptions, "Unable to conclude automatically; the domain has no 'foldAsForall' method and automated generalization failed.")

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

    def specialize(self, specializeMap=None, relabelMap=None, assumptions=USE_DEFAULTS):
        '''
        First attempt to prove that this Forall statement is true under the assumptions,
        and then call specialize on the KnownTruth.
        '''
        return self.prove(assumptions).specialize(specializeMap, relabelMap, assumptions=assumptions)

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's forallEvaluation method
        '''
        assert self.hasDomain(), "Cannot automatically evaluate a forall statement with no domain"

        if len(list(self.instanceVarLists())) == 1:
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
        # raise NotImplementedError("Need to update") # temporarily commented out 12/03/2019 by wdc
        from ._axioms_ import forallInBool
        print('self.allInstanceVars = %s'%str(self.allInstanceVars()))          # for testing; delete later
        # changing the following 3 lines to use allInstanceVars instead of instanceVars
        # P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        # Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        # return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xMulti:self.instanceVars, S:self.domain})
        P_op, P_op_sub = Operation(P, self.allInstanceVars()), self.instanceExpr
        print('P_op = %s'%str(P_op))                                            # for testing; delete later
        print('P_op_sub = %s'%str(P_op_sub))                                    # for testing; delete later
        Q_op, Q_op_sub = Operation(Qmulti, self.allInstanceVars), self.conditions
        return forallInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xMulti:self.allInstanceVars, S:self.domain})

    def unraveled(self):
        remainingConditions = self.conditions
        expr = self.instanceExpr
        for ivar in reversed(self.instanceVars):
            localConditions = [conditions for conditions in remainingConditions if ivar in conditions.freeVars()]
            expr = Forall(ivar, expr, conditions=localConditions)
            remainingConditions = [conditions for conditions in remainingConditions if conditions not in localConditions]
        return expr
