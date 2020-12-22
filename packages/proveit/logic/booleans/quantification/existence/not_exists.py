from proveit import OperationOverInstances
from proveit import Literal, Operation, USE_DEFAULTS
from proveit import P, Q, S


class NotExists(OperationOverInstances):
    # operator of the NotExists operation
    _operator_ = Literal(
        string_format='notexists',
        latex_format=r'\nexists',
        theory=__file__)

    def __init__(self, instance_param_or_params, instance_expr, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, _lambda_map=None):
        '''
        Create a exists (there exists) expression:
        exists_{instance_param_or_params | conditions} instance_expr
        This expresses that there exists a value of the instance parameters(s)
        for which the optional condition(s) is/are satisfied and the
        instance_expr is true.  The instance parameters(s) and condition(s) may
        be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(
            self,
            NotExists._operator_,
            instance_param_or_params,
            instance_expr,
            domain=domain,
            domains=domains,
            condition=condition,
            conditions=conditions,
            _lambda_map=_lambda_map)

    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for a NotExists operation.
        '''
        yield self.unfold  # unfolded form: Not(Exists(..))

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        Derive and return Not(Exists_{x | Q(x)} P(x)) from NotExists_{x | Q(x)} P(x)
        '''
        from . import not_exists_unfolding
        P_op, P_op_sub = Operation(P, self.instance_vars), self.instance_expr
        Q_op, Q_op_sub = Etcetera(
            Operation(Q, self.instance_vars)), self.conditions
        return not_exists_unfolding.instantiate(
            {
                P_op: P_op_sub,
                Q_op: Q_op_sub,
                x_multi: self.instance_vars,
                S: self.domain}).derive_conclusion(assumptions)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return some NotExists_{x | Q(x)} P(x) assuming Not(Exists_{x | Q(x)} P(x)).
        This is automatically derived; see Not.derive_side_effects(..) and Not.derive_not_exists(..).
        '''
        from . import not_exists_folding
        P_op, P_op_sub = Operation(P, self.instance_vars), self.instance_expr
        Q_op, Q_op_sub = Etcetera(
            Operation(Q, self.instance_vars)), self.conditions
        folding = not_exists_folding.instantiate(
            {P_op: P_op_sub, Q_op: Q_op_sub, x_multi: self.instance_vars, S: self.domain})
        return folding.derive_conclusion(assumptions)

    """
    # MUST BE UPDATED
    def conclude_via_forall(self):
        '''
        Prove and return either some NotExists_{x | Q(x)} Not(P(x)) or NotExists_{x | Q(x)} P(x)
        assuming forall_{x | Q(x)} P(x) or assuming forall_{x | Q(x)} (P(x) != TRUE) respectively.
        '''
        from . import forall_implies_not_exists_not, exists_def_negation
        from proveit.logic.equality.eq_ops import NotEquals
        from bool_ops import Not
        from bool_set import TRUE
        Q_op, Q_op_sub = Operation(Q, self.instance_vars), self.conditions
        operand = self.operans[0]
        if isinstance(self.instance_expr, Not):
            P_op, P_op_sub = Operation(P, self.instance_vars), self.instance_expr.etc_expr
            assumption = Forall(operand.arguments, operand.expression.etc_expr, operand.domain_condition)
            return forall_implies_not_exists_not.instantiate({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instance_vars}).derive_conclusion().checked({assumption})
        else:
            P_op, P_op_sub = Operation(P, self.instance_vars), self.instance_expr
            assumption = Forall(operand.arguments, NotEquals(operand.expression, TRUE), operand.domain_condition)
            return exists_def_negation.instantiate({P_op:P_op_sub, Q_op:Q_op_sub, x:self.instance_vars}).derive_left_via_equality().checked({assumption})
    """
