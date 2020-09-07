from proveit import USE_DEFAULTS, maybeFencedString
from proveit._common_ import q
from proveit.logic import Membership
from proveit.number.sets.number_set import NumberSet, NumberMembership

class RationalsSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'Rationals', r'\mathbb{Q}',
                           context=__file__)

    def membershipObject(self, element):
        return RationalsMembership(element, self)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalsInBool
        from proveit._common_ import x
        return xInRationalsInBool.specialize(
                {x:member}, assumptions=assumptions)
    
class RationalsPosSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'NaturalsPos', r'\mathbb{Q}^+',
                           context=__file__)

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
        return xInRationalsPosInBool.specialize(
                {x:member}, assumptions=assumptions)

class RationalsNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'NaturalsNeg', r'\mathbb{Q}^-',
                           context=__file__)

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
        return xInRationalsNegInBool.specialize(
                {x:member}, assumptions=assumptions)

class RationalsNonNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'NaturalsNonNeg', r'\mathbb{Q}^{\geq 0}',
                           context=__file__)

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
        return xInRationalsNonNegInBool.specialize(
                {x:member}, assumptions=assumptions)


class RationalsMembership(NumberMembership):
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)
        
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
    from ._theorems_ import (rationalsInReals,
                             rationalsPosInRationals,
                             rationalsNegInRationals,
                             rationalsNonNegInRationals,
                             rationalsPosInRationalsNonNeg,
                             zeroInRationals)
except:
    pass
