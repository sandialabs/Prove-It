from proveit import USE_DEFAULTS
from proveit.logic import Membership, Nonmembership
from proveit.numbers import num
from proveit._common_ import m, A, x

class UnionMembership(Membership):
    '''
    Defines methods that apply to membership in a unification of sets. 
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
        Deduce and return and [element in (A union B ...)] = [(element in A) or (element in B) ...]
        where self = (A union B ...).
        '''
        from ._axioms_ import unionDef
        element = self.element
        operands = self.domain.operands
        return unionDef.instantiate({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element in (A union B ...)], derive and return [(element in A) or (element in B) ...],
        where self represents (A union B ...). 
        '''
        from ._theorems_ import membershipUnfolding
        from proveit.numbers import num
        element = self.element
        operands = self.domain.operands
        return membershipUnfolding.instantiate({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From either [element in A] or [element in B] ..., derive and return [element in (A union B ...)],
        where self represents (A union B ...). 
        '''
        from ._theorems_ import membershipFolding
        from proveit.numbers import num
        element = self.element
        operands = self.domain.operands
        return membershipFolding.instantiate({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)
                        
class UnionNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an unification of sets. 
    '''
    
    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def sideEffects(self, judgment):
        '''
        Currently non side-effects for union nonmembership.
        '''
        return
        yield

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element not in (A union B ...)] = [(element not in A) and (element not in B) ...]
        where self = (A union B ...).
        '''
        from ._theorems_ import nonmembershipEquiv
        from proveit.numbers import num
        element = self.element
        operands = self.domain.operands
        return nonmembershipEquiv.instantiate({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [element not in A] and [element not in B] ..., derive and return [element not in (A union B ...)],
        where self represents (A union B ...). 
        '''
        from ._theorems_ import nonmembershipFolding
        from proveit.numbers import num
        element = self.element
        operands = self.domain.operands
        return nonmembershipFolding.instantiate({m:num(len(operands)), x:element, A:operands}, assumptions=assumptions)
