from proveit import USE_DEFAULTS, maybeFencedString
from proveit._common_ import q
from proveit.logic import Membership
from proveit.number.sets.number_set import NumberSet, NumberMembership

class RationalsSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'Rationals', r'\mathbb{Q}',
                           context=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in Rationals' for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReals(member, assumptions)
    
    def membershipObject(self, element):
        return RationalsMembership(element, self)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalsInBool
        from proveit._common_ import x
        return xInRationalsInBool.instantiate(
                {x:member}, assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.real._theorems_ import rationalsInReals
        return rationalsInReals.deriveSupersetMembership(member, assumptions)

class RationalsPosSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalsPos', r'\mathbb{Q}^+',
                           context=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalsPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInRationals(member, 
                                                                assumptions)
    
    def membershipObject(self, element):
        return RationalsMembership(element, self)
    
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
        from ._theorems_ import xInRationalsPosInBool
        from proveit._common_ import x
        return xInRationalsPosInBool.instantiate(
                {x:member}, assumptions=assumptions)

    def deduceMemberInRationals(self, member, assumptions=USE_DEFAULTS):
        return rationalsPosInRationals.deriveSupersetMembership(member, assumptions)

class RationalsNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalsNeg', r'\mathbb{Q}^-',
                           context=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalsNeg' 
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInRationals(member, 
                                                                assumptions)
    
    def membershipObject(self, element):
        return RationalsMembership(element, self)

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
        from ._theorems_ import xInRationalsNegInBool
        from proveit._common_ import x
        return xInRationalsNegInBool.instantiate(
                {x:member}, assumptions=assumptions)

    def deduceMemberInRationals(self, member, assumptions=USE_DEFAULTS):
        return rationalsNegInRationals.deriveSupersetMembership(
                member, assumptions)

class RationalsNonNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalsNonNeg', r'\mathbb{Q}^{\geq 0}',
                           context=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalsNonNeg' 
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInRationals(member, 
                                                                assumptions)
    
    def membershipObject(self, element):
        return RationalsMembership(element, self)
        
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
        from ._theorems_ import xInRationalsNonNegInBool
        from proveit._common_ import x
        return xInRationalsNonNegInBool.instantiate(
                {x:member}, assumptions=assumptions)
    
    def deduceMemberInRationals(self, member, assumptions=USE_DEFAULTS):
        return rationalsNonNegInRationals.deriveSupersetMembership(
                member, assumptions)


class RationalsMembership(NumberMembership):
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)
    
    def conclude(self, assumptions):
        from proveit.logic import InSet
        from proveit.number import (
                Rationals, RationalsPos, RationalsNeg, RationalsNonNeg,
                Less, Greater, GreaterEq, zero)
        
        # If we known the element is in Q, we may be able to
        # prove that is in RationalsPos, RationalsNeg, or 
        # RationalsNonNeg if we know its relation to zero.
        if (self.number_set != Rationals and 
                InSet(self.element, Rationals).proven(assumptions)):
            if self.number_set == RationalsPos:
                if Greater(self.element, zero).proven(assumptions):
                    from ._theorems_ import positiveRationalInRationalsPos
                    return positiveRationalInRationalsPos.instantiate(
                            {q:self.element}, assumptions=assumptions)
            if self.number_set == RationalsNeg:
                if Less(self.element, zero).proven():
                    from ._theorems_ import negativeRationalInRationalsNeg
                    return negativeRationalInRationalsNeg.instantiate(
                            {q:self.element}, assumptions=assumptions)                
            if self.number_set == RationalsNonNeg:
                if GreaterEq(self.element, zero).proven():
                    from ._theorems_ import nonNegRationalInRationalsNeg
                    return nonNegRationalInRationalsNeg.instantiate(
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
        For the RationalsPos set, use "a in N"; otherwise, use "a in Z".
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
        For the RationalsPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        '''
        from proveit.number import RationalsPos
        from ._theorems_ import reducedNatsPosRatio

        if self.number_set == RationalsPos:
            return reducedNatsPosRatio.instantiate(
                    {q:self.element}, assumptions=assumptions).choose(
                        numerator_var, denominator_var)
        else:
            raise NotImplementedError(
                    "choose_reduced_rational_fraction() implemented only "
                    "for the RationalsPos NumberSet (but the {0} NumberSet "
                    "was provided instead).".format(self.number_set))


try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for
    # the first time, but fine after that.
    from ._theorems_ import (rationalsPosInRationals,
                             rationalsNegInRationals,
                             rationalsNonNegInRationals,
                             rationalsPosInRationalsNonNeg,
                             zeroInRationals)
except:
    pass
