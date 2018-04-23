from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import x, A, B, Amulti

class Intersect(Operation):
    # operator of the Intersect operation
    _operator_ = Literal(stringFormat='intersect', latexFormat=r'\cap', context=__file__)    
    
    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        Operation.__init__(self, Intersect._operator_, operands)

    def membershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element in (A intersect B ...)] = [(element in A) and (element in B) ...]
        where self = (A intersect B ...).
        '''
        from _axioms_ import intersectDef
        return intersectDef.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def nonmembershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element not in (A intersect B ...)] = [(element not in A) or (element not in B) ...]
        where self = (A intersect B ...).
        '''
        from _theorems_ import nonMembershipEquiv
        return nonMembershipEquiv.specialize({x:element, Amulti:self.operands})
                                    
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A intersection B ...)], derive and return [(element in A) and (element in B) ...],
        where self represents (A intersection B ...). 
        '''
        from _axioms_ import membershipUnfolding
        return membershipUnfolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)
            
    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in A] and [element in B] ..., derive and return [element in (A intersection B ...)],
        where self represents (A intersection B ...). 
        '''
        from _axioms_ import membershipFolding
        return membershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def deduceNonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From either [element not in A] or [element not in B] ..., derive and return [element not in (A intersection B ...)],
        where self represents (A intersection B ...). 
        '''
        from _axioms_ import nonmembershipFolding
        return nonmembershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

