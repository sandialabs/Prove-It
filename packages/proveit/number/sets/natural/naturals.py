import proveit
from proveit import USE_DEFAULTS, maybeFencedString
from proveit.logic import Membership
from proveit.number.sets.number_set import NumberSet
from proveit._common_ import n

class NaturalSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Natural', r'\mathbb{N}', theory=__file__)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.natural._theorems_ import naturalLowerBound
        return naturalLowerBound.instantiate({n:member}, assumptions=assumptions)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in Natural' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberLowerBound(member, assumptions)
        yield lambda assumptions : self.deduceMemberInInt(member, assumptions)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.natural._theorems_ import xInNatInBool
        from proveit._common_ import x
        return xInNatInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInInt(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.integer._theorems_ import natInInt
        return natInInt.deriveSupersetMembership(member, assumptions)


class NaturalPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'NaturalPos', r'\mathbb{N}^+', theory=__file__)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.natural._theorems_ import naturalPosLowerBound
        return naturalPosLowerBound.instantiate({n:member}, assumptions=assumptions)

    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in NaturalPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberLowerBound(member, assumptions)
        yield lambda assumptions : self.deduceMemberInNats(member, assumptions)
        yield lambda assumptions : self.deduce_member_non_zero(member, assumptions)

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
        from proveit.number.sets.natural._theorems_ import xInNatPosInBool
        from proveit._common_ import x
        return xInNatPosInBool.instantiate({x:member}, assumptions=assumptions)
    
    def deduceMemberInNats(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.natural._theorems_ import natPosInNat
        return natPosInNat.deriveSupersetMembership(member, assumptions)

    def deduce_member_non_zero(self, member, assumptions=USE_DEFAULTS):
        from proveit.number.sets.natural._theorems_ import nonZeroIfInNaturalPos
        _n = nonZeroIfInNaturalPos.instanceParam
        return nonZeroIfInNaturalPos.instantiate(
                {_n:member}, assumptions=assumptions)

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from proveit.number.sets.natural._theorems_ import natPosInNat
    from proveit.number.sets.integer._theorems_ import natInInt, natPosInInt

# if proveit.defaults.automation:
#     try:
#         # Import some fundamental theorems without quantifiers that are
#         # imported when automation is used.
#         # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
#         from ._theorems_ import natPosInNat, natInInt, natPosInInt
#     except:
#         pass
