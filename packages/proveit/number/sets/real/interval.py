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
    _operator_ = Literal(stringFormat='IntervalOO',theory=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalOO._operator_,lowerBound,upperBound)
        
    def string(self, **kwargs):
        return '('+self.lowerBound.string() +','+ self.upperBound.string()+')'

    def latex(self, **kwargs):
        return (r'\left('+self.lowerBound.latex() + ','
                + self.upperBound.latex()+r'\right)')

    def deduceElemInSet(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalOO
        return in_IntervalOO.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOO_lower_bound
        return intervalOO_lower_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOO_upper_bound
        return intervalOO_upper_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalOO_in_Reals
        return all_in_IntervalOO_in_Reals.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalOO
        return rescale_in_IntervalOO.instantiate(
            {a:self.lowerBound, b:self.upperBound, c:scaleFactor, x:member},
            assumptions=assumptions)

    def deduceLeftRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_left
        return relax_IntervalOO_left.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceRightRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_right
        return relax_IntervalOO_right.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceLeftRightRelaxedMembership(self, member,
                                         assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_left_right
        return relax_IntervalOO_left_right.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

class IntervalOC(RealInterval):
    # operator of the IntervalOC operation.
    _operator_ = Literal(stringFormat='IntervalOC',theory=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalOC._operator_,lowerBound,upperBound)
                    
    def string(self, **kwargs):
        return '('+self.lowerBound.string() +','+ self.upperBound.string()+']'

    def latex(self, **kwargs):
        return (r'\left('+self.lowerBound.latex() + ','
                + self.upperBound.latex()+r'\right]')
        
    def deduceElemInSet(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalOC
        return in_IntervalOC.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOC_lower_bound
        return intervalOC_lower_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalOC_upper_bound
        return intervalOC_upper_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalOC_in_Reals
        return all_in_IntervalOC_in_Reals.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalOC
        return rescale_in_IntervalOC.instantiate(
                {a:self.lowerBound, b:self.upperBound, c:scaleFactor, x:member},
                assumptions=assumptions)

    def deduceRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOC
        return relax_IntervalOC.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

class IntervalCO(RealInterval):
    # operator of the IntervalCO operation.
    _operator_ = Literal(stringFormat='IntervalCO',theory=__file__)   

    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalCO._operator_,lowerBound,upperBound)
             
    def string(self, **kwargs):
        return '['+self.lowerBound.string() +','+ self.upperBound.string()+')'

    def latex(self, **kwargs):
        return (r'\left['+self.lowerBound.latex() + ','
                + self.upperBound.latex()+r'\right)')

    def deduceElemInSet(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalCO
        return in_IntervalCO.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCO_lower_bound
        return intervalCO_lower_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCO_upper_bound
        return intervalCO_upper_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalCO_in_Reals
        return all_in_IntervalCO_in_Reals.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalCO
        return rescale_in_IntervalCO.instantiate(
                {a:self.lowerBound, b:self.upperBound, c:scaleFactor, x:member},
                assumptions=assumptions)

    def deduceRelaxedMembership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalCO
        return relax_IntervalCO.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

class IntervalCC(RealInterval):
    # operator of the IntervalCC operation.
    _operator_ = Literal(stringFormat='IntervalCC',theory=__file__)   
    
    def __init__(self,lowerBound,upperBound):
        RealInterval.__init__(self,IntervalCC._operator_,lowerBound,upperBound)
                    
    def string(self, **kwargs):
        return '['+self.lowerBound.string() +','+ self.upperBound.string()+']'

    def latex(self, **kwargs):
        return (r'\left['+self.lowerBound.latex() +','
               + self.upperBound.latex()+r'\right]')

    def deduceElemInSet(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalCC
        return in_IntervalCC.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCC_lower_bound
        return intervalCC_lower_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)
    
    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import intervalCC_upper_bound
        return intervalCC_upper_bound.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceMemberInReals(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_IntervalCC_in_Reals
        return all_in_IntervalCC_in_Reals.instantiate(
                {a:self.lowerBound, b:self.upperBound, x:member},
                assumptions=assumptions)

    def deduceRescaledMembership(self, member, scaleFactor,
                                 assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_in_IntervalCC
        return rescale_in_IntervalCC.instantiate(
            {a:self.lowerBound, b:self.upperBound, c:scaleFactor, x:member},
            assumptions=assumptions)

