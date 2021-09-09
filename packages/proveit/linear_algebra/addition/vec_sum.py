from proveit import defaults, Literal, Lambda, relation_prover
from proveit import f, x, K, S, V
from proveit.abstract_algebra import GroupSum
from proveit.linear_algebra import VecSpaces

class VecSum(GroupSum):
    '''
    Denote general summation over a set of elements of any field in 
    analogy to number summation.
    '''
    
    # operator of the Sum operation.
    _operator_ = Literal(string_format='Sum',  latex_format=r'\sum',
                         theory=__file__)
        
    def __init__(self, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        '''
        GroupSum.__init__(self, VecSum._operator_, index_or_indices, summand,
                          domain=domain, domains=domains,
                          condition=condition, conditions=conditions,
                          styles=styles, _lambda_map=_lambda_map)

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field=None,
                            **defaults_config):
        '''
        Prove that this vector summation is in a vector space.
        '''
        from . import summation_closure
        if vec_space is None:
            with defaults.temporary() as tmp_defaults:
                tmp_defaults.assumptions = (defaults.assumptions + 
                                            self.conditions.entries)
                vec_space = VecSpaces.known_vec_space(self.summand, 
                                                      field=field)
        _V = vec_space
        _K = VecSpaces.known_field(_V)
        _x = self.instance_var
        _f = Lambda(self.instance_var, self.summand)
        _S = self.domain
        return summation_closure.instantiate(
                {K:_K, f:_f, S:_S, V:_V, x:_x}).derive_consequent()