from proveit import Literal, Operation

class RealInterval(Operation):
    r'''
    Base class for all permutations of closed and open intervals.  
    Do not construct an object of this class directly!  Instead, use IntervalOO or IntervalOC etc.
    '''
    def __init__(self,operator,lowerBound,upperBound):
        Operation.__init__(self,operator,(lowerBound,upperBound))
        self.lowerBound = lowerBound
        self.upperBound = upperBound
                
class IntervalOO(RealInterval):
    # operator of the IntervalOO operation.
    _operator_ = Literal(stringFormat='IntervalOO',context=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalOO._operator_,lowerBound,upperBound)
        
    def string(self, **kwargs):
        return '('+self.lowerBound.string() +','+ self.upperBound.string()+')'

    def latex(self, **kwargs):
        return r'\left('+self.lowerBound.latex() +','+ self.upperBound.latex()+r'\right)'

    def deduceElemInSet(self, member):
        from real.theorems import inIntervalOO
        return inIntervalOO.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOOLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOOLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOOUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOOUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInReals(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalOO_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalOO_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalOO
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalOO.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

    def deduceLeftRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalOOleft
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalOOleft.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRightRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalOOright
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalOOright.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

class IntervalOC(RealInterval):
    # operator of the IntervalOC operation.
    _operator_ = Literal(stringFormat='IntervalOC',context=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalOC._operator_,lowerBound,upperBound)
                    
    def string(self, **kwargs):
        return '('+self.lowerBound.string() +','+ self.upperBound.string()+']'

    def latex(self, **kwargs):
        return r'\left('+self.lowerBound.latex() +','+ self.upperBound.latex()+r'\right]'
        
    def deduceElemInSet(self, member):
        from real.theorems import inIntervalOC
        return inIntervalOC.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOCLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOCLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalOCUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalOCUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInIntegers(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalOC_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalOC_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalOC
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalOC.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

    def deduceRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalOC
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalOC.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

class IntervalCO(RealInterval):
    # operator of the IntervalCO operation.
    _operator_ = Literal(stringFormat='IntervalCO',context=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalCO._operator_,lowerBound,upperBound)
             
    def string(self, **kwargs):
        return '['+self.lowerBound.string() +','+ self.upperBound.string()+')'

    def latex(self, **kwargs):
        return r'\left['+self.lowerBound.latex() +','+ self.upperBound.latex()+r'\right)'

    def deduceElemInSet(self, member):
        from real.theorems import inIntervalCO
        return inIntervalCO.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCOLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCOLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCOUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCOUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInReals(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalCO_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalCO_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalCO
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalCO.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

    def deduceRelaxedMembership(self, member, assumptions=frozenset()):
        from real.theorems import relaxIntervalCO
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relaxIntervalCO.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

class IntervalCC(RealInterval):
    # operator of the IntervalCC operation.
    _operator_ = Literal(stringFormat='IntervalCC',context=__file__)   
    
    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalCC._operator_,lowerBound,upperBound)
                    
    def string(self, **kwargs):
        return '['+self.lowerBound.string() +','+ self.upperBound.string()+']'

    def latex(self, **kwargs):
        return r'\left['+self.lowerBound.latex() +','+ self.upperBound.latex()+r'\right]'

    def deduceElemInSet(self, member):
        from real.theorems import inIntervalCC
        return inIntervalCC.specialize({a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCCLowerBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCCLowerBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})
    
    def deduceMemberUpperBound(self, member, assumptions=frozenset()):
        from real.theorems import intervalCCUpperBound
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return intervalCCUpperBound.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceMemberInReals(self, member, assumptions=frozenset()):
        from real.theorems import allInIntervalCC_InReals
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return allInIntervalCC_InReals.specialize({a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRescaledMembership(self, member, scaleFactor, assumptions=frozenset()):
        from real.theorems import rescaleInIntervalCC
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        deduceInReals(scaleFactor, assumptions=assumptions)
        return rescaleInIntervalCC.specialize({a:self.lowerBound, b:self.upperBound, c:scaleFactor}).specialize({x:member})

