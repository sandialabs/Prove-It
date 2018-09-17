from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import a, b, n

class Interval(Operation):
    # operator of the Interval operation.
    _operator_ = Literal(stringFormat='Interval',context=__file__)   
    
    r'''
    Contiguous set of integers, from lowerBound to upperBound (both bounds to be interpreted inclusively)
    '''
    def __init__(self, lowerBound, upperBound):
        Operation.__init__(self, Interval._operator_, (lowerBound, upperBound))
        self.lowerBound = lowerBound
        self.upperBound = upperBound
        
    def string(self, **kwargs):
        return '{'+self.lowerBound.string() +'...'+ self.upperBound.string()+'}'

    def latex(self, **kwargs):
        return r'\{'+self.lowerBound.latex() +' \dots '+ self.upperBound.latex()+r'\}'
        
    def deduceElemInSet(self, member):
        from ._theorems_ import inInterval
        return inInterval.specialize({a:self.lowerBound, b:self.upperBound, n:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from ._theorems_ import intervalLowerBound
        return intervalLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from ._theorems_ import intervalUpperBound
        return intervalUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        from ._theorems_ import allInInterval_InInts, allInInterval_InNats, allInInterval_InNatsPos

    def deduceMemberInIntegers(self, member, assumptions=frozenset()):
        from ._theorems_ import allInDiscreteInterval_InInts
        return allInDiscreteInterval_InInts.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInNaturals(self, member, assumptions=frozenset()):
        from ._theorems_ import allInDiscreteInterval_InNats
        from numberSets import deduceInNaturals
        deduceInNaturals(self.lowerBound, assumptions=assumptions)
        deduceInNaturals(self.upperBound, assumptions=assumptions)
        return allInDiscreteInterval_InNats.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInNaturalsPos(self, member, assumptions=frozenset()):
        from ._theorems_ import allInDiscreteInterval_InNatsPos
        return allInDiscreteInterval_InNatsPos.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberIsPositive(self, member, assumptions=frozenset()):
        from ._theorems_ import allInPositiveIntervalArePositive
        return allInPositiveIntervalArePositive.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})        
        
    def deduceMemberIsNegative(self, member, assumptions=frozenset()):
        from ._theorems_ import allInNegativeIntervalAreNegative
        return allInNegativeIntervalAreNegative.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})        
