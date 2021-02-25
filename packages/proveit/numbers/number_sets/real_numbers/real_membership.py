from proveit import defaults, USE_DEFAULTS
from proveit import a
from proveit.logic import NotEquals, InSet
from proveit.numbers import Less, LessEq, greater, greater_eq
from proveit.numbers import (zero, Real, RealPos, RealNeg, RealNonNeg,
                             RealNonPos, RealNonZero)
from proveit.numbers.number_sets.number_set import NumberMembership

class RealNonZeroMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNonZero
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNonZero)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Real).proven(assumptions) and
                NotEquals(self.element, zero).proven(assumptions)):
            return self.conclude_as_last_resort(assumptions)
        return NumberMembership.conclude(self, assumptions)

    def conclude_as_last_resort(self, assumptions=USE_DEFAULTS):
        '''
        Conclude element in RealNonZero by proving it is real
        and not zero.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import nonzero_real_is_real_nonzero
        return nonzero_real_is_real_nonzero.instantiate(
            {a:self.element}, assumptions=assumptions)


class RealPosMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealPos
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealPos)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Real).proven(assumptions) and
                greater(self.element, zero).proven(assumptions)):
            return self.conclude_as_last_resort(assumptions)
        return NumberMembership.conclude(self, assumptions)

    def conclude_as_last_resort(self, assumptions=USE_DEFAULTS):
        '''
        Conclude element in Real by proving it is real and positive.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import pos_real_is_real_pos
        return pos_real_is_real_pos.instantiate(
            {a:self.element}, assumptions=assumptions)

        
class RealNegMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNeg
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNeg)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Real).proven(assumptions) and
                Less(self.element, zero).proven(assumptions)):
            return self.conclude_as_last_resort(assumptions)
        return NumberMembership.conclude(self, assumptions)

    def conclude_as_last_resort(self, assumptions=USE_DEFAULTS):
        '''
        Conclude element in Real by proving it is real and negative.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import neg_real_is_real_neg
        return neg_real_is_real_neg.instantiate(
            {a:self.element}, assumptions=assumptions)


class RealNonNegMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNonNeg
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNonNeg)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Real).proven(assumptions) and
                greater_eq(self.element, zero).proven(assumptions)):
            return self.conclude_as_last_resort(assumptions)
        return NumberMembership.conclude(self, assumptions)

    def conclude_as_last_resort(self, assumptions=USE_DEFAULTS):
        '''
        Conclude element in Real by proving it is real and non-negative.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import nonneg_real_is_real_nonneg
        return nonneg_real_is_real_nonneg.instantiate(
            {a:self.element}, assumptions=assumptions)


class RealNonPosMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNonPos
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNonPos)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Real).proven(assumptions) and
                LessEq(self.element, zero).proven(assumptions)):
            return self.conclude_as_last_resort(assumptions)
        return NumberMembership.conclude(self, assumptions)

    def conclude_as_last_resort(self, assumptions=USE_DEFAULTS):
        '''
        Conclude element in Real by proving it is real and non-positive.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import nonpos_real_is_real_nonpos
        return nonpos_real_is_real_nonpos.instantiate(
            {a:self.element}, assumptions=assumptions)
