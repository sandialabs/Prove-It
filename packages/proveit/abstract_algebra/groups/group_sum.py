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
        from proveit.numbers import Interval
        # MUST BE UPDATED TO DEAL WITH 'joining' NESTED LEVELS
        fence = kwargs['fence'] if 'fence' in kwargs else False
        if isinstance(self.domain, Interval):
            lower = self.domain.lower_bound.formatted(format_type)
            upper = self.domain.upper_bound.formatted(format_type)
            formatted_inner = self.operator.formatted(
                format_type) + r'_{' + self.index.formatted(format_type) + '=' + lower + r'}' + r'^{' + upper + r'} '
            explicit_ivars = list(self.explicit_instance_vars())
            has_explicit_ivars = (len(explicit_ivars) > 0)
            explicit_conds = list(self.explicit_conditions())
            has_explicit_conds = (len(explicit_conds) > 0)
            if has_explicit_conds:
                if has_explicit_ivars:
                    formatted_inner += " | "
                formatted_inner += ', '.join(condition.formatted(format_type)
                                             for condition in explicit_conds)
            formatted_inner += self.summand.formatted(format_type, fence=True)
            return maybe_fenced(format_type, formatted_inner, fence=fence)
        else:
            return OperationOverInstances._formatted(self, format_type, 
                                                     fence=fence)
