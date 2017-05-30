from proveit import Literal

class NaturalsSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'Naturals', r'\mathbb{N}', context=__file__)
    
    def deduceMemberLowerBound(self, member):
        from natural.theorems import naturalsLowerBound
        return naturalsLowerBound.specialize({n:member})  

class NaturalsPosSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'NaturalsPos', r'\mathbb{N}^+', context=__file__)
    
    def deduceMemberLowerBound(self, member):
        from natural.theorems import naturalsPosLowerBound
        return naturalsPosLowerBound.specialize({n:member})  
