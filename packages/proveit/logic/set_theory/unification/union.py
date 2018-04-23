from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import A, B, x, Amulti
        
class Union(Operation):
    # operator of the Intersect operation
    _operator_ = Literal(stringFormat='union', latexFormat=r'\cup', context=__file__)    
    
    def __init__(self, *operands):
        '''
        Union any number of sets: A union B union C
        '''
        Operation.__init__(self, Union._operator_, operands)
    
    def membershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element in (A union B ...)] = [(element in A) or (element in B) ...]
        where self = (A union B ...).
        '''
        from _axioms_ import unionDef
        return unionDef.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def nonmembershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element not in (A union B ...)] = [(element not in A) and (element not in B) ...]
        where self = (A union B ...).
        '''
        from _theorems_ import nonmembershipEquiv
        return nonmembershipEquiv.specialize({x:element, Amulti:self.operands})
                
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A union B ...)], derive and return [(element in A) or (element in B) ...],
        where self represents (A union B ...). 
        '''
        from _theorems_ import membershipUnfolding
        return membershipUnfolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From either [element in A] or [element in B] ..., derive and return [element in (A union B ...)],
        where self represents (A union B ...). 
        '''
        from _theorems_ import membershipFolding
        return membershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def deduceNonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element not in A] and [element not in B] ..., derive and return [element not in (A union B ...)],
        where self represents (A union B ...). 
        '''
        from _theorems_ import nonmembershipFolding
        return nonmembershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)
