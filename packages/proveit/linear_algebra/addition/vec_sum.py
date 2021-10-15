from proveit import (defaults, Literal, Lambda, relation_prover,
                     equality_prover)
from proveit import IndexedVar, ExprTuple, ExprRange
from proveit import b, f, j, K, Q, V, k, x
from proveit.logic import InSet
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

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this ScalarMult
        expression assuming the operands have been simplified.
        
        Handles doubly-nested scalar multiplication.
        '''
        from proveit.numbers import Complex
        inner_assumptions = defaults.assumptions + self.conditions.entries
        if hasattr(self.summand, 'deduce_in_number_set'):
            self.summand.deduce_in_number_set(
                    Complex, assumptions=inner_assumptions)
        if InSet(self.summand, Complex).proven(assumptions=inner_assumptions):
            # If the operands are all complex numbers, this will
            # VecAdd will reduce to number Add.
            return self.number_sum_reduction()
        return GroupSum.shallow_simplification(
                self, must_evaluate=must_evaluate)

    @equality_prover('number_sum_reduced', 'number_sum_reduce')
    def number_sum_reduction(self, **defaults_config):
        from . import scalar_sum_extends_number_sum
        _b = self.indices
        _f = Lambda(_b, self.summand)
        _Q = Lambda(_b, self.condition)
        _j = _b.num_elements()
        impl = scalar_sum_extends_number_sum.instantiate(
                {j:_j, b:_b, f:_f, Q:_Q})
        return impl.derive_consequent()

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
        if not hasattr(self, 'condition'):
            print(self)
        _Q = Lambda(self.indices, self.condition)
        return summation_closure.instantiate(
                {j:_j, K:_K, f:_f, Q:_Q, V:_V, b:_b}).derive_consequent()
