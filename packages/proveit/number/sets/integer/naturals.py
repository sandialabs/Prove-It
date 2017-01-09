from proveit import Literal

class NaturalsSet(Literal):
    def __init__(self, pkg):
        Literal.__init__(self, pkg, 'Naturals', r'\mathbb{N}')
    
    def deduceMemberLowerBound(self, member):
        from natural.theorems import naturalsLowerBound
        return naturalsLowerBound.specialize({n:member})  

class NaturalsPosSet(Literal):
    def __init__(self, pkg):
        Literal.__init__(self, pkg, 'NaturalsPos', r'\mathbb{N}^+')
    
    def deduceMemberLowerBound(self, member):
        from natural.theorems import naturalsPosLowerBound
        return naturalsPosLowerBound.specialize({n:member})  

Naturals = NaturalsSet(__package__)
NaturalsPos = NaturalsPosSet(__package__)
