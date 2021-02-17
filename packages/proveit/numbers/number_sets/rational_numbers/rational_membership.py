from proveit import USE_DEFAULTS
from proveit import q
from proveit.logic import NotEquals, InSet
from proveit.numbers.number_sets.number_set import NumberMembership

class RationalMembership(NumberMembership):
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    def conclude(self, assumptions):
        from proveit.logic import InSet, NotEquals
        from proveit.numbers import (
            Rational, RationalNonZero, RationalPos, RationalNeg,
            RationalNonNeg, Less, greater, greater_eq, zero)

        # If we known the element is in Q, we may be able to
        # prove that is in RationalNonZero, RationalPos, RationalNeg, or
        # RationalNonNeg if we know its relation to zero.
        if (self.number_set != Rational and
                InSet(self.element, Rational).proven(assumptions)):
            if self.number_set == RationalNonZero:
                if NotEquals(self.element, zero).proven(assumptions):
                    from . import nonzero_rational_is_rational_nonzero
                    return nonzero_rational_is_rational_nonzero.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalPos:
                if greater(self.element, zero).proven(assumptions):
                    from . import positive_rational_is_rational_pos
                    return positive_rational_is_rational_pos.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalNeg:
                if Less(self.element, zero).proven():
                    from . import negative_rational_is_rational_neg
                    return negative_rational_is_rational_neg.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalNonNeg:
                if greater_eq(self.element, zero).proven():
                    from . import nonneg_rational_in_rational_neg
                    return nonneg_rational_in_rational_neg.instantiate(
                        {q: self.element}, assumptions=assumptions)

        # Resort to the default NumberMembership.conclude strategies.
        return NumberMembership.conclude(self, assumptions)

    def choose_rational_fraction(self, numerator_var, denominator_var,
                                 *, assumptions=USE_DEFAULTS):
        '''
        Choose Skolem "constants" (really variables with proper a
        ssumptions) for
            x = a/b, either "a in Z" or "a in N", b in N
        where x is the element in the rationals set, a and b are the
        Skolem "constants".
        For the RationalPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        '''
        pass

    def choose_reduced_rational_fraction(self, numerator_var, denominator_var,
                                         *, assumptions=USE_DEFAULTS):
        '''
        Choose Skolem "constants" (Rationally variables with proper a
        ssumptions) for
            x = a/b, either "a in Z" or "a in N", b in N, gcd(a, b) = 1
        where x is the element in the rationals set, a and b are the
        Skolem "constants".
        For the RationalPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        '''
        from . import reduced_nat_pos_ratio
        from proveit.numbers import RationalPos

        if self.number_set == RationalPos:
            return reduced_nat_pos_ratio.instantiate(
                {q: self.element}, assumptions=assumptions).choose(
                numerator_var, denominator_var)
        else:
            raise NotImplementedError(
                "choose_reduced_rational_fraction() implemented only "
                "for the RationalPos NumberSet (but the {0} NumberSet "
                "was provided instead).".format(self.number_set))


class RationalNonZeroMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNonZero
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNonZero
        RationalMembership.__init__(self, element, RationalNonZero)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Rational, zero
        if (InSet(self.element, Rational).proven(assumptions) and
                NotEquals(self.element, zero).proven(assumptions)):
            from . import nonzero_rational_is_rational_nonzero
            return nonzero_rational_is_rational_nonzero.instantiate(
                    {q:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)


class RationalPosMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalPos
    '''

    def __init__(self, element):
        from proveit.numbers import RationalPos
        RationalMembership.__init__(self, element, RationalPos)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Rational, greater, zero
        if (InSet(self.element, Rational).proven(assumptions) and
                greater(self.element, zero).proven(assumptions)):
            from . import pos_rational_is_rational_pos
            return pos_rational_is_rational_pos.instantiate(
                    {q:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)

        
class RationalNegMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNeg
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNeg
        RationalMembership.__init__(self, element, RationalNeg)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Rational, Less, zero
        if (InSet(self.element, Rational).proven(assumptions) and
                Less(self.element, zero).proven(assumptions)):
            from . import neg_rational_is_rational_neg
            return neg_rational_is_rational_neg.instantiate(
                    {q:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)


class RationalNonNegMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNonNeg
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNonNeg
        RationalMembership.__init__(self, element, RationalNonNeg)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Rational, greater_eq, zero
        if (InSet(self.element, Rational).proven(assumptions) and
                greater_eq(self.element, zero).proven(assumptions)):
            from . import nonneg_rational_is_rational_nonneg
            return nonneg_rational_is_rational_nonneg.instantiate(
                    {q:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)


class RationalNonPosMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNonPos
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNonPos
        RationalMembership.__init__(self, element, RationalNonPos)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Rational, LessEq, zero
        if (InSet(self.element, Rational).proven(assumptions) and
                LessEq(self.element, zero).proven(assumptions)):
            from . import nonpos_rational_is_rational_nonpos
            return nonpos_rational_is_rational_nonpos.instantiate(
                    {q:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)
