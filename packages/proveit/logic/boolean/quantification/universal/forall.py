from proveit import (Literal, Operation, OperationOverInstances, 
                     ExprTuple, ExprRange, IndexedVar,
                     defaults, USE_DEFAULTS, ProofFailure)
from proveit._common_ import k, n, x, P, S
from proveit._core_.proof import Generalization

class Forall(OperationOverInstances):
    # operator of the Forall operation
    _operator_ = Literal(stringFormat='forall', latexFormat=r'\forall', context=__file__)
    
    def __init__(self, instanceParamOrParams, instanceExpr, *,
                 domain=None, domains=None, condition=None, 
                 conditions=None, _lambda_map=None):
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
        OperationOverInstances.__init__(
                self, Forall._operator_, instanceParamOrParams, 
                instanceExpr, domain=domain, domains=domains,
                condition=condition, conditions=conditions, 
                #nestMultiIvars=True, _lambda_map=_lambda_map)
                nestMultiIvars=False, _lambda_map=_lambda_map)
        
    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for this forall operation.
        '''
        if hasattr(self, 'instanceParam') and self.hasDomain() and hasattr(self.domain, 'unfoldForall'):
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
        if self.hasDomain() and hasattr(self.first_domain(), 'foldAsForall'):
            # try foldAsForall first
            try:
                return self.concludeAsFolded(assumptions)
            except:
                raise ProofFailure(self, assumptions, 
                                   "Unable to conclude automatically; "
                                   "the 'foldAsForall' method on the "
                                   "domain failed.")
        else:
            # If there is no 'foldAsForall' strategy to try, we can
            # attempt a different non-trivial strategy of proving
            # via generalization with automation.
            try:
                conditions = list(self.inclusiveConditions())
                proven_inst_expr = self.explicitInstanceExpr().prove(
                        assumptions=assumptions + tuple(conditions))
                instanceParamLists = [list(self.explicitInstanceParams())]
                # see if we can generalize multiple levels 
                # simultaneously for a shorter proof
                while isinstance(proven_inst_expr.proof(), Generalization):
                    new_params = proven_inst_expr.explicitInstanceParams()
                    instanceParamLists.append(list(new_params))
                    conditions += proven_inst_expr.conditions
                    proven_inst_expr = proven_inst_expr.proof().requiredTruths[0]
                return proven_inst_expr.generalize(instanceParamLists, 
                                                   conditions=conditions)
            except ProofFailure:
                raise ProofFailure(self, assumptions, 
                                   "Unable to conclude automatically; "
                                   "the domain has no 'foldAsForall' method "
                                   "and automated generalization failed.")
                    
            
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
        Conclude this forall statement from an "unfolded" version 
        dependent upon the domain of the forall,
        calling foldAsForall on the condition.
        For example, conclude 
        forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''
        assert self.hasDomain(), "Cannot fold a forall statement with no domain"
        if len(self.instanceParams) > 1:
            # When there are more than one instance variables, we
            # must conclude the unbundled form first and the
            # derive the bundled form from that.
            unbundled = self.unbundle_equality(assumptions=assumptions).rhs
            unbundled = unbundled.concludeAsFolded(assumptions)
            return unbundled.bundle(assumptions=assumptions)
        blah = self.domain.foldAsForall(self, assumptions)
        return blah
    
    def bundle(self, num_levels=2, *, assumptions=USE_DEFAULTS):
        '''
        Given a nested forall, derive an equivalent form in which a 
        given number of nested levels is bundled together.
        
        For example,
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        can become
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        via bundle with num_levels=2.
        '''
        from proveit import bundle # generic for OperationOverInstances
        from ._theorems_ import bundle as bundle_thm
        return bundle(self, bundle_thm, num_levels=num_levels, 
                      assumptions=assumptions)

    def bundle_equality(self, num_levels=2, *, assumptions=USE_DEFAULTS):
        '''
        Given a nested forall, equate it with an equivalent form in 
        which a given number of nested levels is bundled together.
        
        For example,
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        can be equated with
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        via bundle with num_levels=2.
        '''
        from proveit import bundle # generic for OperationOverInstances
        from ._theorems_ import bundling
        return bundle(self, bundling, num_levels=num_levels, 
                      assumptions=assumptions)


    def unbundle(self, num_param_entries=(1,), *, assumptions=USE_DEFAULTS):
        '''
        From a nested forall, derive an equivalent form in which the 
        parameter entries are split in number according to
        'num_param_entries'.
        
        For example,
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        can become
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        via bundle with num_param_entries=(2, 1) or 
        num_param_entries=(2,) -- the last number can be implied
        by the remaining number of parameters.
        '''
        from proveit import unbundle # generic for OperationOverInstances
        from ._theorems_ import unbundle as unbundle_thm
        return unbundle(self, unbundle_thm, 
                        num_param_entries=num_param_entries, 
                        assumptions=assumptions)
    
    def unbundle_equality(self, num_param_entries=(1,), *,
                          assumptions=USE_DEFAULTS):
        '''
        From a nested forall, equate it with an equivalent form in 
        which the parameter entries are split in number according to
        'num_param_entries'.
        
        For example,
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        can equate with
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        via bundle with num_param_entries=(2, 1) or 
        num_param_entries=(2,) -- the last number can be implied
        by the remaining number of parameters.
        '''
        from proveit import unbundle # generic for OperationOverInstances
        from ._theorems_ import bundling
        return unbundle(self, bundling, num_param_entries=num_param_entries, 
                        assumptions=assumptions)

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
        
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
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
        from proveit.number import one
        from ._axioms_ import forall_in_bool
        _x = self.instanceParams
        P_op, _P_op = Operation(P, _x), self.instanceExpr
        _n = _x.length(assumptions)
        x_1_to_n = ExprTuple(ExprRange(k, IndexedVar(x, k), one, _n))
        return forall_in_bool.specialize(
                {n:_n, P_op:_P_op, x_1_to_n:_x},
                assumptions=assumptions)
