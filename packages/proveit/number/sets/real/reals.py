from proveit import USE_DEFAULTS
from proveit._common_ import a
from proveit.number.sets.number_set import NumberSet

class RealsSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Reals',r'\mathbb{R}', context=__file__)
    
class RealsPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsPos', r'\mathbb{R}^+', context=__file__)
    
    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from real.theorems import inRealsPos_iff_positive
        return inRealsPos_iff_positive.specialize({a:member},assumptions=assumptions).deriveRightImplication(assumptions)    

class RealsNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealsNeg', r'\mathbb{R}^-', context=__file__)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from real.theorems import inRealsNeg_iff_negative
        return inRealsNeg_iff_negative.specialize({a:member},assumptions=assumptions).deriveRightImplication(assumptions)
    
class RationalsSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Rationals',r'\mathbb{Q}', context=__file__)
    
class RationalsPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RationalsPos', r'\mathbb{Q}^+', context=__file__)
    
    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from real.theorems import inRationalsPos_iff_positive
        return inRationalsPos_iff_positive.specialize({a:member},
                                                      assumptions=assumptions).deriveRightImplication(assumptions)        
        

try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
    from ._theorems_ import realsPosInReals, realsNegInReals, intsInReals, natsInReals, natsPosInReals
except:
    pass
