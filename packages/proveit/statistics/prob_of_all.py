from proveit import (Literal, OperationOverInstances, Operation, ExprTuple,
                     single_or_composite_expression, defaults)
from proveit import x, y, f, P, Q, S


class ProbOfAll(OperationOverInstances):
    '''
    ProbOfAll represents the probability of an event that is defines as
    the set of outcomes of a sample space defined by a condition
    (set comprehension).
    '''
    # operator of the SetOfAll operation
    _operator_ = Literal(string_format='Prob',
                         latex_format=r'\textrm{Prob}', theory=__file__)
    _init_argname_mapping_ = {'instance_element': 'instance_expr'}

    def __init__(self, instance_param_or_params, instance_element,
                 domain=None, *, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        '''
        Create an expression representing the probability of the
        set of all instance_element for instance parameter(s) such that 
        the condition is satisfied:
            Prob_{instance_param(s) | condition(s)} instance_element
        {instance_element | conditions}_{instance_param_or_params \in S}
        '''
        OperationOverInstances.__init__(
            self, ProbOfAll._operator_, instance_param_or_params,
            instance_element, domain=domain, domains=domains,
            condition=condition, conditions=conditions,
            styles=styles, _lambda_map=_lambda_map)
        self.instance_element = self.instance_expr
        if hasattr(self, 'instance_param'):
            if not hasattr(self, 'domain'):
                raise ValueError("ProbOfAll requires a domain")
        elif hasattr(self, 'instance_params'):
            if not hasattr(self, 'domains') or None in self.domains:
                raise ValueError("ProbOfAll requires domains")
        else:
            assert False, ("Expecting either 'instance_param' or 'instance_params' "
                           "to be set")
