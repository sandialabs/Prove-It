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
        return xInRationalsInBool.specialize({x:member}, assumptions=assumptions)
    
class RationalsPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RationalsPos', r'\mathbb{Q}^+', context=__file__)
    
    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInRationalsPosInBool
        from proveit._common_ import x
        return xInRationalsPosInBool.specialize({x:member}, assumptions=assumptions)
    
    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from real.theorems import inRationalsPos_iff_positive
        return inRationalsPos_iff_positive.specialize({a:member},
                                                      assumptions=assumptions).deriveRightImplication(assumptions)

# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from ._theorems_ import rationalsPosInRationals, intsInRationals, natsInRationals, natsPosInRationals

if proveit.defaults.automation:
    try:
        # Import some fundamental theorems without quantifiers that are
        # imported when automation is used.
        # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
        from ._theorems_ import rationalsPosInRationals, intsInRationals, natsInRationals, natsPosInRationals
    except:
        pass
