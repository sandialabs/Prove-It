import proveit
from proveit import USE_DEFAULTS, maybeFencedString
from proveit._common_ import a
from proveit.number.sets.number_set import NumberSet

class RationalsSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Rationals',r'\mathbb{Q}', context=__file__)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalsInBool
        from proveit._common_ import x
        return xInRationalsInBool.specialize(
                {x:member}, assumptions=assumptions)
    
class RationalsPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RationalsPos', r'\mathbb{Q}^+',
                           context=__file__)
    
    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalsPosInBool
        from proveit._common_ import x
        return xInRationalsPosInBool.specialize(
                {x:member}, assumptions=assumptions)
    
    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from real.theorems import inRationalsPos_iff_positive
        return inRationalsPos_iff_positive.specialize(
                {a:member},
                assumptions=assumptions).deriveRightImplication(assumptions)

class RationalsNonNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RationalsNonNeg', r'\mathbb{Q}^{\ge 0}',
                context=__file__)
    
    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalsNonNegInBool
        from proveit._common_ import x
        return xInRationalsNonNegInBool.specialize(
                {x:member}, assumptions=assumptions)
    
    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import inRationalsNonNeg_iff_nonNeg
        return inRationalsNonNeg_iff_nonNeg.specialize(
                {q:member}, assumptions=assumptions).deriveRightImplication(
                        assumptions)

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from ._theorems_ import (
        natsInRationals, natsInRationalsNonNeg, natsPosInRationals,
        natsPosInRationalsNonNeg, intsInRationals, rationalsPosInRationals,
        rationalsPosInRationalsNonNeg, rationalsNonNegInRationals)
