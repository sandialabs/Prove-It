from proveit import Literal

class RealsSet(Literal):
    def __init__(self, pkg):
        Literal.__init__(self, pkg, 'Reals',r'\mathbb{R}')
    
class RealsPosSet(Literal):
    def __init__(self, pkg):
        Literal.__init__(self, pkg, 'RealsPos', r'\mathbb{R}^+')
    
    def deduceMemberLowerBound(self, member):
        from real.theorems import inRealsPos_iff_positive
        return inRealsPos_iff_positive.specialize({a:member}).deriveRightImplication()    

class RealsNegSet(Literal):
    def __init__(self, pkg):
        Literal.__init__(self, pkg, 'RealsNeg', r'\mathbb{R}^-')
    
    def deduceMemberUpperBound(self, member):
        from real.theorems import inRealsNeg_iff_negative
        return inRealsNeg_iff_negative.specialize({a:member}).deriveRightImplication()    

Reals = Literal(__package__,'Reals',r'\mathbb{R}')    
RealsPos = RealsPosSet(__package__)
RealsNeg = RealsNegSet(__package__)
