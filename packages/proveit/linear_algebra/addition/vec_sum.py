from proveit import defaults, Literal, Lambda, relation_prover
from proveit import IndexedVar, ExprTuple, ExprRange
from proveit import b, f, j, K, Q, V, k, x
from proveit.numbers import one
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
        _b = self.indices
        _j = _b.num_elements()
        _f = Lambda(self.indices, self.summand)
        _Q = Lambda(self.indices, self.condition)
        # Need to distinguish two cases: _j == 1 vs. _j > 1, b/c we are
        # not allowed to construct a single-element ExprRange
        if _j == one:
            b_1_to_j = IndexedVar(b, one)  # we are subbing for x_1
            _b = _b[0]                     # using a bare elem
        else:
            b_1_to_j = ExprTuple(ExprRange(k, IndexedVar(x, k), one, _j))
        return summation_closure.instantiate(
                {j:_j, K:_K, f:_f, Q:_Q, V:_V, b_1_to_j:_b}).derive_consequent()
