import proveit
from proveit.logic import Equals, NotEquals
from proveit import USE_DEFAULTS, maybeFencedString
from proveit._common_ import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet

class RealSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Real',r'\mathbb{R}', theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInComplex(member, 
                                                                assumptions)
    
    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRealInBool
        return xInRealInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInComplex(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.complex_numbers._theorems_ import realInComplex
        return realInComplex.deriveSupersetMembership(member, assumptions)

class RealPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealPos', r'\mathbb{R}^+', theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReal(member, assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import inRealPos_iff_positive
        return inRealPos_iff_positive.instantiate(
                {a:member},assumptions=assumptions).deriveRightImplication(
                        assumptions)

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
        from ._theorems_ import xInRealPosInBool
        from proveit._common_ import x
        return xInRealPosInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInReal(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import realPosInReal
        return realPosInReal.deriveSupersetMembership(member, assumptions)

class RealNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealNeg', r'\mathbb{R}^-', theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNeg' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReal(member, assumptions)

    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import inRealNeg_iff_negative
        return inRealNeg_iff_negative.instantiate(
                {a:member},assumptions=assumptions).deriveRightImplication(
                        assumptions)

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
        from ._theorems_ import xInRealNegInBool
        from proveit._common_ import x
        return xInRealNegInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInReal(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import realNegInReal
        return realNegInReal.deriveSupersetMembership(member, assumptions)

class RealNonNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealNonNeg', r'\mathbb{R}^{\ge 0}',
                           theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonNeg' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReal(member, assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import inRealNonNeg_iff_non_negative
        return inRealNonNeg_iff_non_negative.instantiate(
                {a:member},assumptions=assumptions).deriveRightImplication(
                        assumptions)

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
        from ._theorems_ import xInRealNonNegInBool
        from proveit._common_ import x
        return xInRealNonNegInBool.instantiate({x:member},
                                               assumptions=assumptions)

    def deduceMemberInReal(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import realNonNegInReal
        return realNonNegInReal.deriveSupersetMembership(member, assumptions)

# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from ._theorems_ import (
#         realPosInReal, realNegInReal, realNonNegInReal, intInReal,
#         natInReal, natPosInReal, natPosInRealPos)

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    try:
        # This can fails before running the _axioms_ and _theorems_
        # notebooks for the first time, but fine after that.
        from ._theorems_ import (
            realPosInReal, realNegInReal, realNonNegInReal,
            rationalInReal,
            intInReal, natInReal, natPosInReal, natPosInRealPos,
            natInRealNonNeg, natPosInRealNonNeg,
            realPosInRealNonNeg)
    except:
        pass
