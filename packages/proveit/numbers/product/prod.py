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

    @classmethod
    def _create_instance_expr_with_condition(cls, instance_expr, condition):
        '''
        The condition for set comprehension is effected via a
        Conditional. That is, ∏_{x | Q(x)} f(x) is a stylized
        form of ∏_{x} [{f(x) if Q(x). {1 if ¬Q(x).]
        '''
        from proveit import Conditional
        from proveit.core_expr_types import ConditionalSet
        from proveit.logic import Not
        from proveit.numbers import one
        return ConditionalSet(Conditional(instance_expr, condition),
                              Conditional(one, Not(condition)))
        
    @classmethod
    def _extract_condition_and_instance_expr(cls, lambda_body):
        '''
        The condition for set comprehension is effected via a
        Conditional. That is, ∏_{x | Q(x)} f(x) is a stylized
        form of ∏_{x} [{f(x) if Q(x). {0 if ¬Q(x).]
        Return the condition and instance_expr as a tuple.  For the example,
        this would return (Q(x), f(x)).
        '''
        from proveit.core_expr_types import ConditionalSet
        from proveit.logic import Not
        from proveit.numbers import one
        if isinstance(lambda_body, ConditionalSet):
            if len(lambda_body.conditionals) == 2 and (
                    lambda_body.conditionals[1].condition == 
                    Not(lambda_body.conditionals[0].condition) and
                    lambda_body.conditionals[1].value == one):
                return (lambda_body.conditionals[0].condition, 
                        lambda_body.conditionals[0].value)
        raise NotImplementedError("How to handle product over %s?"%lambda_body)