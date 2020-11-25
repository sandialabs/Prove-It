from proveit import USE_DEFAULTS
from proveit.logic import Membership, Nonmembership
from proveit.number import num
from proveit._common_ import m, x, A

class IntersectMembership(Membership):
    '''
    Defines methods that apply to membership in an intersection of sets. 
    '''
    
    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain
    
    def sideEffects(self, judgment):
        '''
        Unfold the enumerated set membership as a side-effect.
        '''
        yield self.unfold
    
    def equivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element in (A intersect B ...)] = [(element in A) and (element in B) ...]
        where self = (A intersect B ...).
        '''
        from ._axioms_ import intersectionDef
        element = self.element
        operands = self.domain.operands
        return intersectionDef.specialize({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element in (A intersection B ...)], derive and return [(element in A) and (element in B) ...],
        where self represents (A intersection B ...). 
        '''
        from ._theorems_ import membershipUnfolding
        from proveit.number import num
        element = self.element
        operands = self.domain.operands
        return membershipUnfolding.specialize({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [element in A], [element in B] ..., derive and return [element in (A intersection B ...)],
        where self represents (A intersection B ...). 
        '''
        from ._theorems_ import membershipFolding
        from proveit.number import num
        element = self.element
        operands = self.domain.operands
        return membershipFolding.specialize({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)
                        
class IntersectNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an intersection of sets. 
    '''
    
    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain
    
    def sideEffects(self, judgment):
        '''
        Currently non side-effects for intersection nonmembership.
        '''
        return
        yield

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element not in (A intersect B ...)] = [(element not in A) or (element not in B) ...]
        where self = (A intersect B ...).
        '''
        from ._theorems_ import nonmembershipEquiv
        from proveit.number import num
        element = self.element
        operands = self.domain.operands
        return nonmembershipEquiv.specialize({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From either [element not in A] or [element not in B] ..., derive and return [element not in (A intersection B ...)],
        where self represents (A intersection B ...). 
        '''
        from ._theorems_ import nonmembershipFolding
        from proveit.number import num
        element = self.element
        operands = self.domain.operands
        return nonmembershipFolding.specialize({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)
