from proveit import (Literal, OperationOverInstances, Operation, ExprTuple,
                     single_or_composite_expression, USE_DEFAULTS)
from proveit._common_ import x, y, f, P, Q, S


class UnionAll(OperationOverInstances):
    # operator of the UnionOfAll operation
    _operator_ = Literal(
        string_format='union_of_all',
        latex_format=r'\bigcup',
        theory=__file__)
    _init_argname_mapping_ = {'instance_element': 'instance_expr'}

    def __init__(self, instance_param_or_params, instance_element,
                 domain=None, *, domains=None, condition=None,
                 conditions=None, _lambda_map=None):
        '''
        Create an expression representing the union of all
        instance_element for instance parameter(s) such that the conditions
        are satisfied:
        {instance_element | conditions}_{instance_param_or_params \in S}
        '''
        OperationOverInstances.__init__(
            self,
            UnionAll._operator_,
            instance_param_or_params,
            instance_element,
            domain=domain,
            domains=domains,
            condition=condition,
            conditions=conditions,
            _lambda_map=_lambda_map)
        self.instance_element = self.instance_expr
        if hasattr(self, 'instance_param'):
            if not hasattr(self, 'domain'):
                raise ValueError("SetOfAll requires a domain")
        elif hasattr(self, 'instance_params'):
            if not hasattr(self, 'domains') or None in self.domains:
                raise ValueError("SetOfAll requires a domain(s)")
        else:
            assert False, ("Expecting either 'instance_param' or 'instance_params' "
                           "to be set")
