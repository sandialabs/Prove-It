from proveit import Literal, OperationOverInstances


class Prod(OperationOverInstances):
    # operator of the Prod operation.
    _operator_ = Literal(
        string_format='Prod',
        latex_format=r'prod',
        theory=__file__)

#    def __init__(self, summand-instance_expression, indices-instance_vars, domains):
#    def __init__(self, instance_vars, instance_expr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, indices, summand, domain, *, condition=None,
                 conditions=None, styles=None):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in basiclogic.booleanss):
        indices: instance vars
        summand: instance_expressions
        domains: conditions (except no longer optional)
        '''
        OperationOverInstances.__init__(
            self, Prod._operator_, indices, summand, domain=domain,
            condition=condition, conditions=conditions,
            styles=styles)
