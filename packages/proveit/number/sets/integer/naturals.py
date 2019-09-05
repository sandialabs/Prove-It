from proveit import USE_DEFAULTS, maybeFencedString
from proveit.logic import Membership
from proveit.number.sets.number_set import NumberSet

class NaturalsSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Naturals', r'\mathbb{N}', context=__file__)
    
    def deduceMemberLowerBound(self, member):
        from ._theorems_ import naturalsLowerBound
        return naturalsLowerBound.specialize({n:member})  

class NaturalsPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'NaturalsPos', r'\mathbb{N}^+', context=__file__)
    
    def deduceMemberLowerBound(self, member):
        from ._theorems_ import naturalsPosLowerBound
        return naturalsPosLowerBound.specialize({n:member})  
    
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

try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
    from ._theorems_ import natsPosInNats, natsInInts, natsPosInInts
except:
    pass
