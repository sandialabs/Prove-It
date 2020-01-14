from proveit import USE_DEFAULTS, maybeFencedString
from proveit.logic import Membership
from proveit.number.sets.number_set import NumberSet
from proveit._common_ import n

class NaturalsSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Naturals', r'\mathbb{N}', context=__file__)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import naturalsLowerBound
        return naturalsLowerBound.specialize({n:member}, assumptions=assumptions)

    def membershipSideEffects(self, knownTruth):
        '''
        Yield side-effects when proving 'n in Naturals' for a given n.
        '''
        member = knownTruth.element
        yield lambda assumptions : self.deduceMemberLowerBound(member, assumptions)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInNatsInBool
        from proveit._common_ import x
        return xInNatsInBool.specialize({x:member}, assumptions=assumptions)


class NaturalsPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'NaturalsPos', r'\mathbb{N}^+', context=__file__)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import naturalsPosLowerBound
        return naturalsPosLowerBound.specialize({n:member}, assumptions=assumptions)

    def membershipSideEffects(self, knownTruth):
        '''
        Yield side-effects when proving 'n in NaturalsPos' for a given n.
        '''

        member = knownTruth.element
        yield lambda assumptions : self.deduceMemberLowerBound(member, assumptions)

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
        from ._theorems_ import xInNatsPosInBool
        from proveit._common_ import x
        return xInNatsPosInBool.specialize({x:member}, assumptions=assumptions)

try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
    from ._theorems_ import natsPosInNats, natsInInts, natsPosInInts
except:
    pass
