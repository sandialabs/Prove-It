from proveit import (Literal, OperationOverInstances, Operation, ExprTuple,
                     singleOrCompositeExpression, USE_DEFAULTS)
from proveit._common_ import x, y, f, P, Q, S

class IntersectAll(OperationOverInstances):
    # operator of the UnionOfAll operation
    _operator_ = Literal(stringFormat='intersect_all', latexFormat=r'\bigcap', context=__file__)  
    _init_argname_mapping_ = {'instanceElement':'instanceExpr'}

    def __init__(self, instanceParamOrParams, instanceElement,
                 domain=None, *, domains=None, condition=None,
                 conditions=None, _lambda_map=None):
        '''
        Create an expression representing the union of all
        instanceElement for instance parameter(s) such that the conditions
        are satisfied:
        {instanceElement | conditions}_{instanceParamOrParams \in S}
        '''
        OperationOverInstances.__init__(
                self, IntersectAll._operator_, instanceParamOrParams,
                instanceElement, domain=domain, domains=domains,
                condition=condition, conditions=conditions, _lambda_map=_lambda_map)
        self.instanceElement = self.instanceExpr
        if hasattr(self, 'instanceParam'):
            if not hasattr(self, 'domain'):
                raise ValueError("SetOfAll requires a domain")
        elif hasattr(self, 'instanceParams'):
            if not hasattr(self, 'domains') or None in self.domains:
                raise ValueError("SetOfAll requires domains")
        else:
            assert False, ("Expecting either 'instanceParam' or 'instanceParams' "
                           "to be set")

