from proveit import (Lambda, Conditional, OperationOverInstances, Judgment,
                     composite_expression, prover, relation_prover)
from proveit import defaults, Literal, Function, ExprTuple, USE_DEFAULTS
from proveit import n, x, y, z, A, B, P, Q, R, S, Px


class UniqueExists(OperationOverInstances):
    # operator of the Exists operation
    _operator_ = Literal(
        string_format='exists!',
        latex_format=r'\exists!',
        theory=__file__)

    def __init__(self, instance_param_or_params, instance_expr, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        '''
        Create a exists (there exists) expression:
        exists_{instance_param_or_params | condition} instance_expr
        This expresses that there exists a value of the instance parameters(s)
        for which the optional condition(s) is/are satisfied and the
        instance_expr is true.  The instance parameter(s) and condition(s) may
        be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(
            self, UniqueExists._operator_, instance_param_or_params, instance_expr,
            domain=domain, domains=domains, condition=condition,
            conditions=conditions, _lambda_map=_lambda_map, styles=styles)

    @classmethod
    def _create_instance_expr_with_condition(cls, instance_expr, condition):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, unique_exists_{x | Q(x)} P(x) is a stylized
        form of unique_exists_{x} [Q(x) ∧ P(x).]
        Return the conjunction (e.g., Q(x) ∧ P(x) in the example).
        '''
        from proveit.logic import And
        return And(condition, instance_expr)
        
    @classmethod
    def _extract_condition_and_instance_expr(cls, lambda_body):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, unique_exists_{x | Q(x)} P(x) is a stylized
        form of unique_exists_{x} [Q(x) ∧ P(x).]
        Return the condition and instance_expr as a tuple.  For the example,
        this would return (Q(x), P(x)).
        '''
        from proveit.logic import And
        if isinstance(lambda_body, And) and lambda_body.operands.is_double():
            return tuple(lambda_body.operands)
        return None, lambda_body