import proveit
from proveit import prover
from proveit import a, x
from proveit.numbers.number_sets.number_set import NumberSet


class IntegerSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Integer', r'\mathbb{Z}', 
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .integer_membership import IntegerMembership    
        return IntegerMembership(element)


class IntegerNonZeroSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerNonZero', r'\mathbb{Z}^{\neq 0}', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerNonZeroMembership    
        return IntegerNonZeroMembership(element)


class IntegerNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerNeg', r'\mathbb{Z}^{-}', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerNegMembership    
        return IntegerNegMembership(element)


class IntegerNonPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerNonPos', r'\mathbb{Z}^{\leq 0}', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerNonPosMembership    
        return IntegerNonPosMembership(element)


if proveit.defaults.sideeffect_automation:
    from . import (nat_within_int,
                   nat_pos_within_int,
                   nat_pos_within_nonzero_int,
                   nonzero_int_within_int,
                   neg_int_within_int, neg_int_within_nonzero_int,
                   neg_int_within_nonpos_int,
                   nonpos_int_within_int)
