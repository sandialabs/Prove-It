from proveit import (Literal, OperationOverInstances, Lambda,
                     prover, equality_prover)
from proveit import x, y, f, g, A, B, C, P, Q, R, S, X, Omega


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

    @equality_prover("transformed", "transform")
    def transformation(self, lambda_map, new_domain, sample_space,
                       **defaults_config):
        '''
        Equate this ProbOfAll expression with a new ProbOfAll expression
        with the 'new_domain' using the lambda_map transformation.
        The lambda_map must be a bijection from the new_domain to
        the original domain, and the original mapping must be 1-to-1
        function from the original domain to 'sample_space' which
        must be a sample space.
        '''
        from . import prob_of_all_events_transformation
        _Omega = sample_space
        _A = self.domain
        _B = new_domain
        _Q = Lambda(self.instance_param, self.non_domain_condition())
        _f = Lambda(self.instance_param, self.instance_expr)
        _g = lambda_map
        _x = self.instance_param
        _y = lambda_map.parameter
        return prob_of_all_events_transformation.instantiate(
                {Omega:_Omega, A:_A, B:_B, Q:_Q, f:_f, g:_g, x:_x, y:_y})

    @equality_prover("partitioned", "split")
    def partition(self, A, B, sample_space, **defaults_config):
        '''
        Equate this ProbOfAll expression with the some of two
        ProbOfAll expressions over two disjoint domains whose union is
        the original domain.
        '''
        from . import prob_of_disjoint_events_is_prob_sum
        _Omega = sample_space
        _A = A
        _B = B
        _C = self.domain
        _f = Lambda(self.instance_param, self.instance_expr)
        _Q = Lambda(self.instance_param, self.non_domain_condition())
        
        return prob_of_disjoint_events_is_prob_sum.instantiate(
                {Omega:_Omega, A:_A, B:_B, C:_C, X:_X, Q:_Q, f:_f})

    @equality_prover("computed", "compute")
    def computation(self, sample_space, **defaults_config):
        '''
        The computation of a ProbOfAll equates it with the 
        corresponding summation over sample probabilities as long
        as the function is an injection onto a sample space.
        '''
        from . import prob_of_all_as_sum
        _Omega = sample_space
        _X = self.domain
        _f = Lambda(self.instance_param, self.instance_expr)
        _Q = Lambda(self.instance_param, self.non_domain_condition())
        return prob_of_all_as_sum.instantiate(
                {Omega:_Omega, X:_X, f:_f, Q:_Q, x:self.instance_param})
        
    @equality_prover("computed_via_complement", "compute_via_complement")
    def computation_via_complement(self, complement_prob_of_all, sample_space,
                                   **defaults_config):
        from . import complementary_event_prob_of_all
        if not isinstance(complement_prob_of_all, ProbOfAll):
            raise TypeError("'complement_prob_of_all' should be a ProbOfAll")
        if complement_prob_of_all.domain != self.domain:
            raise ValueError("'complement_prob_of_all' should have the same "
                             "domain: %s ≠ %s"%(complement_prob_of_all.domain,
                                                self.domain))
        _Omega = sample_space
        _X = self.domain
        _f = Lambda(self.instance_param, self.instance_expr)
        _Q = Lambda(self.instance_param, self.non_domain_condition())
        _R = Lambda(complement_prob_of_all.instance_param, 
                    complement_prob_of_all.non_domain_condition())
        _x = self.instance_param
        _y = complement_prob_of_all.instance_param
        impl = complementary_event_prob_of_all.instantiate(
                {Omega:_Omega, X:_X, f:_f, Q:_Q, R:_R, x:_x, y:_y})
        return impl.derive_consequent()
        
        