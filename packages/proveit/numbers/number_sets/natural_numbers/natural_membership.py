from proveit import USE_DEFAULTS
from proveit import a
from proveit.logic import NotEquals, InSet
from proveit.numbers import greater, greater_eq
from proveit.numbers import (zero, Natural, NaturalPos, Integer)
from proveit.numbers.number_sets.number_set import NumberMembership


class NaturalMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RationalNonZero
    '''

    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Integer).proven(assumptions) and
                greater_eq(self.element, zero).proven(assumptions)):
            return self.conclude_as_last_resort(assumptions)
        return NumberMembership.conclude(self, assumptions)

    def conclude_as_last_resort(self, assumptions=USE_DEFAULTS):
        '''
        Conclude element in Natural by proving it is integer
        and non-negative.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from proveit.numbers.number_sets.integers import (
            nonneg_int_is_natural)
        return nonneg_int_is_natural.instantiate(
            {a:self.element}, assumptions=assumptions)


class NaturalPosMembership(NaturalMembership):

    '''
    Defines methods that apply to membership in RationalPos
    '''

    def __init__(self, element):
        NaturalMembership.__init__(self, element, NaturalPos)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Integer).proven(assumptions) and
                greater(self.element, zero).proven(assumptions)):
            return self.conclude_as_last_resort(assumptions)
        return NumberMembership.conclude(self, assumptions)
    
    def conclude_as_last_resort(self, assumptions=USE_DEFAULTS):
        '''
        Conclude element in NaturalPos by proving it is integer
        and positive.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from proveit.numbers.number_sets.integers import (
            pos_int_is_natural_pos)
        return pos_int_is_natural_pos.instantiate(
            {a:self.element}, assumptions=assumptions)
