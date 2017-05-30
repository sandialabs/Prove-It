from proveit import Literal

class RealsSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'Reals',r'\mathbb{R}', context=__file__)
    
class RealsPosSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'RealsPos', r'\mathbb{R}^+', context=__file__)
    
    def deduceMemberLowerBound(self, member):
        from real.theorems import inRealsPos_iff_positive
        return inRealsPos_iff_positive.specialize({a:member}).deriveRightImplication()    

class RealsNegSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'RealsNeg', r'\mathbb{R}^-', context=__file__)
    
    def deduceMemberUpperBound(self, member):
        from real.theorems import inRealsNeg_iff_negative
        return inRealsNeg_iff_negative.specialize({a:member}).deriveRightImplication()    

