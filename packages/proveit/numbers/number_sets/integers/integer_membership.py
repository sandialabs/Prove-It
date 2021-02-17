from proveit import USE_DEFAULTS
from proveit import a
from proveit.logic import NotEquals, InSet
from proveit.numbers import Less, LessEq
from proveit.numbers import (zero, Integer, IntegerNeg,
                             IntegerNonPos, IntegerNonZero)
from proveit.numbers.number_sets.number_set import NumberMembership


class IntegerNonZeroMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RationalNonZero
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerNonZero)

    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Integer).proven(assumptions) and
                NotEquals(self.element, zero).proven(assumptions)):
            from . import nonzero_int_is_int_nonzero
            return nonzero_int_is_int_nonzero.instantiate(
                    {a:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)


class IntegerNegMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RationalPos
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerNeg)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Integer).proven(assumptions) and
                Less(self.element, zero).proven(assumptions)):
            from . import neg_int_is_int_neg
            return neg_int_is_int_neg.instantiate(
                    {a:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)

        
class IntegerNonPosMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RationalNeg
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerNonPos)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Integer).proven(assumptions) and
                LessEq(self.element, zero).proven(assumptions)):
            from . import nonpos_int_is_int_nonpos
            return nonpos_int_is_int_nonpos.instantiate(
                    {a:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)
