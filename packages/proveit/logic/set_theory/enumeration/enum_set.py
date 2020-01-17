from proveit import Literal, Operation, ExprTuple, USE_DEFAULTS
from proveit.abstract_algebra.generic_methods import apply_permutation_thm
from proveit.abstract_algebra.generic_methods import apply_commutation_thm

class Set(Operation):
    '''
    Defines an enumerated set (i.e. a set with explicitly-listed
    elements). For example, one could use Set(one, two, three) to
    produce the enumerated set {1, 2, 3}.
    '''
    
    # operator of the Set operation
    _operator_ = Literal(stringFormat='Set', context=__file__) 
    
    def __init__(self, *elems):
        Operation.__init__(self, Set._operator_, elems)
        self.elements = self.operands
    
    def membershipObject(self, element):
        from .enum_membership import EnumMembership
        return EnumMembership(element, self)

    def nonmembershipObject(self, element):
        from .enum_membership import EnumNonmembership
        return EnumNonmembership(element, self)

    def string(self, **kwargs):
        return '{' + self.elements.string(fence=False) + '}'
    
    def latex(self, **kwargs):
        return r'\left\{' + self.elements.latex(fence=False) + r'\right\}'

    def permutation(self, initIdx=None, finalIdx=None,
                    assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression is set-equivalent to a Set
        in which the element at index initIdx has been moved to
        finalIdx. For example, {a, b, c, d} = {a, c, b, d} via
        initIdx = 1 (i.e. 'b') and finalIdx = -2.
        '''
        from ._theorems_ import (permutation, leftwardPermutation,
                                 rightwardPermutation)
        return apply_commutation_thm(self, initIdx, finalIdx, permutation,
                                     leftwardPermutation, rightwardPermutation,
                                     assumptions)       

