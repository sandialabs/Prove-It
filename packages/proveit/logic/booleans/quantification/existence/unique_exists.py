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
