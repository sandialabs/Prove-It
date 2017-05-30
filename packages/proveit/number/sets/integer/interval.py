from proveit import Literal, BinaryOperation

class Interval(BinaryOperation):
    # operator of the Interval operation.
    _operator_ = Literal(stringFormat='Interval',context=__file__)   
    
    r'''
    Contiguous set of integers, from lowerBound to upperBound (both bounds to be interpreted inclusively)
    '''
    def __init__(self, lowerBound, upperBound):
        BinaryOperation.__init__(self, Interval._operator_, lowerBound, upperBound)
        self.lowerBound = lowerBound
        self.upperBound = upperBound
        
    def string(self, **kwargs):
        return '{'+self.lowerBound.string() +'...'+ self.upperBound.string()+'}'

    def latex(self, **kwargs):
        return r'\{'+self.lowerBound.latex() +' \dots '+ self.upperBound.latex()+r'\}'
        
    def deduceElemInSet(self, member):
        from integer.theorems import inInterval
        return inInterval.specialize({a:self.lowerBound, b:self.upperBound, n:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from integer.theorems import intervalLowerBound
        from numberSets import deduceInIntegers
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        return intervalLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from integer.theorems import intervalUpperBound
        from numberSets import deduceInIntegers
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        return intervalUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInIntegers(self, member, assumptions=frozenset()):
        from integer.theorems import allInDiscreteInterval_InInts
        from numberSets import deduceInIntegers
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        return allInDiscreteInterval_InInts.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInNaturals(self, member, assumptions=frozenset()):
        from natural.theorems import allInDiscreteInterval_InNats
        from numberSets import deduceInNaturals
        deduceInNaturals(self.lowerBound, assumptions=assumptions)
        deduceInNaturals(self.upperBound, assumptions=assumptions)
        return allInDiscreteInterval_InNats.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberInNaturalsPos(self, member, assumptions=frozenset()):
        from natural.theorems import allInDiscreteInterval_InNatsPos
        from numberSets import deduceInNaturalsPos
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        deducePositive(self.lowerBound, assumptions=assumptions)
        return allInDiscreteInterval_InNatsPos.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})

    def deduceMemberIsPositive(self, member, assumptions=frozenset()):
        from integer.theorems import allInPositiveIntervalArePositive
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        deducePositive(self.lowerBound, assumptions=assumptions)
        return allInPositiveIntervalArePositive.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})        
        
    def deduceMemberIsNegative(self, member, assumptions=frozenset()):
        from integer.theorems import allInNegativeIntervalAreNegative
        deduceInIntegers(self.lowerBound, assumptions=assumptions)
        deduceInIntegers(self.upperBound, assumptions=assumptions)
        deduceNegative(self.upperBound, assumptions=assumptions)
        return allInNegativeIntervalAreNegative.specialize({a:self.lowerBound, b:self.upperBound}).specialize({n:member})        
