from proveit import OperationOverInstances, maybe_fenced

class GroupSum(OperationOverInstances):
    '''
    Denote general summation over a set of elements of any group in 
    analogy to number summation.
    '''
    
    _init_argname_mapping_ = {'index_or_indices': 'instance_param_or_params',
                              'summand': 'instance_expr'}

    def __init__(self, operator, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in
        basiclogic.booleanss):
        indices: instance vars
        summand: instance_expressions
        domains: conditions (except no longer optional)
        '''
        if (domains is not None):
            raise NotImplementedError("Sum class not yet implemented for "
                                      "multiple domains nor for multiple "
                                      "indices.")

        OperationOverInstances.__init__(
            self, operator, index_or_indices, summand,
            domain=domain, domains=domains, condition=condition,
            conditions=conditions, styles=styles, _lambda_map=_lambda_map)
        if hasattr(self, 'instance_param'):
            self.index = self.instance_param
        if hasattr(self, 'instance_params'):
            self.indices = self.instance_params
        self.summand = self.instance_expr

    def _formatted(self, format_type, **kwargs):
        from proveit.numbers import Sum
        return Sum._formatted(format_type, **kwargs)
