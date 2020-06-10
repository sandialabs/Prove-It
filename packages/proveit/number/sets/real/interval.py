from proveit import Literal, Operation, USE_DEFAULTS
import proveit._common_
from proveit._common_ import a, b, c, x

class RealInterval(Operation):
    r'''
    Base class for all permutations of closed and open intervals.  
    Do not construct an object of this class directly!
    Instead, use IntervalOO or IntervalOC etc.
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
        return (r'\left('+self.lowerBound.latex() + ','
                + self.upperBound.latex()+r'\right)')

    def deduceElemInSet(self, member):
        from ._theorems_ import in_IntervalOO
        return in_IntervalOO.specialize(
                {a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOO_lower_bound
        return intervalOO_lower_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOO_upper_bound
        return intervalOO_upper_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalOO_in_Reals
        return all_in_IntervalOO_in_Reals.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalOO
        return rescale_in_IntervalOO.specialize(
            {a:self.lowerBound, b:self.upperBound, c:scaleFactor},
            assumptions=assumptions
            ).specialize({x:member}, assumptions=assumptions)

    def deduceLeftRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_left
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relax_IntervalOO_left.specialize(
                {a:self.lowerBound, b:self.upperBound}).specialize({x:member})

    def deduceRightRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_right
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relax_IntervalOO_right.specialize(
                {a:self.lowerBound, b:self.upperBound}).specialize({x:member})

class IntervalOC(RealInterval):
    # operator of the IntervalOC operation.
    _operator_ = Literal(stringFormat='IntervalOC',context=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalOC._operator_,lowerBound,upperBound)
                    
    def string(self, **kwargs):
        return '('+self.lowerBound.string() +','+ self.upperBound.string()+']'

    def latex(self, **kwargs):
        return (r'\left('+self.lowerBound.latex() + ','
                + self.upperBound.latex()+r'\right]')
        
    def deduceElemInSet(self, member):
        from ._theorems_ import in_IntervalOC
        return in_IntervalOC.specialize(
                {a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOC_lower_bound
        return intervalOC_lower_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                    {x:member}, assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOC_upper_bound
        return intervalOC_upper_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalOC_in_Reals
        return all_in_IntervalOC_in_Reals.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalOC
        return rescale_in_IntervalOC.specialize(
                {a:self.lowerBound, b:self.upperBound, c:scaleFactor},
                assumptions=assumptions
                ).specialize({x:member}, assumptions=assumptions)

    def deduceRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOC
        # from proveit.number.numberSets import deduceInReals
        # dIR_lower = deduceInReals(self.lowerBound, assumptions=assumptions)
        # dIR_upper = deduceInReals(self.upperBound, assumptions=assumptions)
        return relax_IntervalOC.specialize(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

class IntervalCO(RealInterval):
    # operator of the IntervalCO operation.
    _operator_ = Literal(stringFormat='IntervalCO',context=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalCO._operator_,lowerBound,upperBound)
             
    def string(self, **kwargs):
        return '['+self.lowerBound.string() +','+ self.upperBound.string()+')'

    def latex(self, **kwargs):
        return (r'\left['+self.lowerBound.latex() + ','
                + self.upperBound.latex()+r'\right)')

    def deduceElemInSet(self, member):
        from ._theorems_ import in_IntervalCO
        return in_IntervalCO.specialize(
                {a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCO_lower_bound
        return intervalCO_lower_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCO_upper_bound
        return intervalCO_upper_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalCO_in_Reals
        return all_in_IntervalCO_in_Reals.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalCO
        return rescale_in_IntervalCO.specialize(
                {a:self.lowerBound, b:self.upperBound, c:scaleFactor},
                assumptions=assumptions
                ).specialize({x:member}, assumptions=assumptions)

    def deduceRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalCO
        from numberSets import deduceInReals
        deduceInReals(self.lowerBound, assumptions=assumptions)
        deduceInReals(self.upperBound, assumptions=assumptions)
        return relax_IntervalCO.specialize(
                {a:self.lowerBound, b:self.upperBound}).specialize({x:member})

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
        from ._theorems_ import in_IntervalCC
        return in_IntervalCC.specialize(
                {a:self.lowerBound, b:self.upperBound, x:member})

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCC_lower_bound
        return intervalCC_lower_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCC_upper_bound
        return intervalCC_upper_bound.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalCC_in_Reals
        return all_in_IntervalCC_in_Reals.specialize(
                {a:self.lowerBound, b:self.upperBound},
                assumptions=assumptions).specialize(
                        {x:member}, assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalCC
        return rescale_in_IntervalCC.specialize(
            {a:self.lowerBound, b:self.upperBound, c:scaleFactor},
            assumptions=assumptions
            ).specialize({x:member}, assumptions=assumptions)

