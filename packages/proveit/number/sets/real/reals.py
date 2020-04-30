import proveit
from proveit import USE_DEFAULTS, maybeFencedString
from proveit._common_ import a
from proveit.number.sets.number_set import NumberSet

class RealSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Reals',r'\mathbb{R}', context=__file__)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRealsInBool
        from proveit._common_ import x
        return xInRealsInBool.specialize({x:member}, assumptions=assumptions)

class RealPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsPos', r'\mathbb{R}^+', context=__file__)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from real.theorems import inRealsPos_iff_positive
        return inRealsPos_iff_positive.specialize({a:member},assumptions=assumptions).deriveRightImplication(assumptions)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRealsPosInBool
        from proveit._common_ import x
        return xInRealsPosInBool.specialize({x:member}, assumptions=assumptions)

class RealNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsNeg', r'\mathbb{R}^-', context=__file__)

    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from real.theorems import inRealsNeg_iff_negative
        return inRealsNeg_iff_negative.specialize({a:member},assumptions=assumptions).deriveRightImplication(assumptions)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRealsNegInBool
        from proveit._common_ import x
        return xInRealsNegInBool.specialize({x:member}, assumptions=assumptions)

class RealNonNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsNonNeg', r'\mathbb{R}^{0^{+}}',
                           context=__file__)
    
    # def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
    #     from real.theorems import inRealsNeg_iff_negative
    #     return inRealsNeg_iff_negative.specialize({a:member},assumptions=assumptions).deriveRightImplication(assumptions)    
    
    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['forceFence'] if 'forceFence' in kwargs else False)       
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['forceFence'] if 'forceFence' in kwargs else False)       
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRealsNonNegInBool
        from proveit._common_ import x
        return xInRealsNonNegInBool.specialize({x:member},
                                               assumptions=assumptions)

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from ._theorems_ import (
        realsPosInReals, realsNegInReals, realsNonNegInReals, intsInReals,
        natsInReals, natsPosInReals, natPosInRealsPos, natsInRealsNonNeg,
        natsPosInRealsNonNeg, realsPosInRealsNonNeg)
