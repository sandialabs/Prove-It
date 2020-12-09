from proveit import USE_DEFAULTS, maybeFencedString
from proveit._common_ import q
from proveit.logic import Membership
from proveit.numbers.sets.number_set import NumberSet, NumberMembership

class RationalSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'Rational', r'\mathbb{Q}',
                           theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in Rational' for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReal(member, assumptions)
    
    def membershipObject(self, element):
        return RationalMembership(element, self)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalInBool
        from proveit._common_ import x
        return xInRationalInBool.instantiate(
                {x:member}, assumptions=assumptions)

    def deduceMemberInReal(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.sets.real._theorems_ import rationalInReal
        return rationalInReal.deriveSupersetMembership(member, assumptions)

class RationalPosSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalPos', r'\mathbb{Q}^+',
                           theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInRational(member, 
                                                                assumptions)
    
    def membershipObject(self, element):
        return RationalMembership(element, self)
    
    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalPosInBool
        from proveit._common_ import x
        return xInRationalPosInBool.instantiate(
                {x:member}, assumptions=assumptions)

    def deduceMemberInRational(self, member, assumptions=USE_DEFAULTS):
        return rationalPosInRational.deriveSupersetMembership(member, assumptions)

class RationalNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNeg', r'\mathbb{Q}^-',
                           theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNeg' 
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInRational(member, 
                                                                assumptions)
    
    def membershipObject(self, element):
        return RationalMembership(element, self)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalNegInBool
        from proveit._common_ import x
        return xInRationalNegInBool.instantiate(
                {x:member}, assumptions=assumptions)

    def deduceMemberInRational(self, member, assumptions=USE_DEFAULTS):
        return rationalNegInRational.deriveSupersetMembership(
                member, assumptions)

class RationalNonNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNonNeg', r'\mathbb{Q}^{\geq 0}',
                           theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonNeg' 
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInRational(member, 
                                                                assumptions)
    
    def membershipObject(self, element):
        return RationalMembership(element, self)
        
    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalNonNegInBool
        from proveit._common_ import x
        return xInRationalNonNegInBool.instantiate(
                {x:member}, assumptions=assumptions)
    
    def deduceMemberInRational(self, member, assumptions=USE_DEFAULTS):
        return rationalNonNegInRational.deriveSupersetMembership(
                member, assumptions)


class RationalMembership(NumberMembership):
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)
    
    def conclude(self, assumptions):
        from proveit.logic import InSet
        from proveit.numbers import (
                Rational, RationalPos, RationalNeg, RationalNonNeg,
                Less, Greater, GreaterEq, zero)
        
        # If we known the element is in Q, we may be able to
        # prove that is in RationalPos, RationalNeg, or 
        # RationalNonNeg if we know its relation to zero.
        if (self.number_set != Rational and 
                InSet(self.element, Rational).proven(assumptions)):
            if self.number_set == RationalPos:
                if Greater(self.element, zero).proven(assumptions):
                    from ._theorems_ import positiveRationalInRationalPos
                    return positiveRationalInRationalPos.instantiate(
                            {q:self.element}, assumptions=assumptions)
            if self.number_set == RationalNeg:
                if Less(self.element, zero).proven():
                    from ._theorems_ import negativeRationalInRationalNeg
                    return negativeRationalInRationalNeg.instantiate(
                            {q:self.element}, assumptions=assumptions)                
            if self.number_set == RationalNonNeg:
                if GreaterEq(self.element, zero).proven():
                    from ._theorems_ import nonNegRationalInRationalNeg
                    return nonNegRationalInRationalNeg.instantiate(
                            {q:self.element}, assumptions=assumptions)   

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
        Choose Skolem "constants" (really variables with proper a
        ssumptions) for 
            x = a/b, either "a in Z" or "a in N", b in N, gcd(a, b) = 1
        where x is the element in the rationals set, a and b are the
        Skolem "constants".
        For the RationalPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        '''
        from proveit.numbers import RationalPos
        from ._theorems_ import reducedNatPosRatio

        if self.number_set == RationalPos:
            return reducedNatPosRatio.instantiate(
                    {q:self.element}, assumptions=assumptions).choose(
                        numerator_var, denominator_var)
        else:
            raise NotImplementedError(
                    "choose_reduced_rational_fraction() implemented only "
                    "for the RationalPos NumberSet (but the {0} NumberSet "
                    "was provided instead).".format(self.number_set))


try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for
    # the first time, but fine after that.
    from ._theorems_ import (rationalPosInRational,
                             rationalNegInRational,
                             rationalNonNegInRational,
                             rationalPosInRationalNonNeg,
                             zeroInRational)
except:
    pass
