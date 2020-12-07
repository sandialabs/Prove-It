import proveit
from proveit.logic import Equals, NotEquals
from proveit import USE_DEFAULTS, maybeFencedString
from proveit._common_ import a, x, y
from proveit.number.sets.number_set import NumberSet

class RealSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Reals',r'\mathbb{R}', theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealsPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInComplexes(member, 
                                                                assumptions)
    
    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRealsInBool
        return xInRealsInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInComplexes(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.complex._theorems_ import realsInComplexes
        return realsInComplexes.deriveSupersetMembership(member, assumptions)

class RealPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsPos', r'\mathbb{R}^+', theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealsPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReals(member, assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import inRealsPos_iff_positive
        return inRealsPos_iff_positive.instantiate(
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
        from ._theorems_ import xInRealsPosInBool
        from proveit._common_ import x
        return xInRealsPosInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import realsPosInReals
        return realsPosInReals.deriveSupersetMembership(member, assumptions)

class RealNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsNeg', r'\mathbb{R}^-', theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealsNeg' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReals(member, assumptions)

    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import inRealsNeg_iff_negative
        return inRealsNeg_iff_negative.instantiate(
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
        from ._theorems_ import xInRealsNegInBool
        from proveit._common_ import x
        return xInRealsNegInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import realsNegInReals
        return realsNegInReals.deriveSupersetMembership(member, assumptions)

class RealNonNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsNonNeg', r'\mathbb{R}^{\ge 0}',
                           theory=__file__)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealsNonNeg' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInReals(member, assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import inRealsNonNeg_iff_non_negative
        return inRealsNonNeg_iff_non_negative.instantiate(
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
        from ._theorems_ import xInRealsNonNegInBool
        from proveit._common_ import x
        return xInRealsNonNegInBool.instantiate({x:member},
                                               assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import realsNonNegInReals
        return realsNonNegInReals.deriveSupersetMembership(member, assumptions)

# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from ._theorems_ import (
#         realsPosInReals, realsNegInReals, realsNonNegInReals, intInReals,
#         natInReals, natPosInReals, natPosInRealsPos)

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    try:
        # This can fails before running the _axioms_ and _theorems_
        # notebooks for the first time, but fine after that.
        from ._theorems_ import (
            realsPosInReals, realsNegInReals, realsNonNegInReals,
            rationalsInReals,
            intInReals, natInReals, natPosInReals, natPosInRealsPos,
            natInRealsNonNeg, natPosInRealsNonNeg,
            realsPosInRealsNonNeg)
    except:
        pass
