from proveit import Literal, AssociativeOperation, USE_DEFAULTS
from proveit.common import A, B, x, Amulti
        
class Union(AssociativeOperation):
    # operator of the Intersect operation
    _operator_ = Literal(stringFormat='union', latexFormat=r'\cup', context=__file__)    
    
    def __init__(self, *operands):
        '''
        Union any number of sets: A union B union C
        '''
        AssociativeOperation.__init__(self, Union._operator_, *operands)
    
    def membershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element in (A union B ...)] = [(element in A) or (element in B) ...]
        where self = (A union B ...).
        '''
        from _axioms_ import unionDef
        from _theorems_ import membershipEquiv
        if len(self.operands) == 2:       
            return unionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]})
        else:
            return membershipEquiv.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def nonMembershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element not in (A union B ...)] = [(element not in A) and (element not in B) ...]
        where self = (A union B ...).
        '''
        from _axioms_ import binaryNonMembershipEquiv
        from _theorems_ import nonMembershipEquiv
        if len(self.operands) == 2:       
            return binaryNonMembershipEquiv.specialize({x:element, A:self.operands[0], B:self.operands[1]})
        else:
            return nonMembershipEquiv.specialize({x:element, Amulti:self.operands})
                
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A union B ...)], derive and return [(element in A) or (element in B) ...],
        where self represents (A union B ...). 
        '''
        from _theorems_ import binaryMembershipUnfolding, membershipUnfolding
        if len(self.operands) == 2:
            return binaryMembershipUnfolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            return membershipUnfolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From either [element in A] or [element in B] ..., derive and return [element in (A union B ...)],
        where self represents (A union B ...). 
        '''
        from _theorems_ import binaryMembershipFolding, membershipFolding
        if len(self.operands) == 2:
            return binaryMembershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:      
            return membershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def deduceNonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element not in A] and [element not in B] ..., derive and return [element not in (A union B ...)],
        where self represents (A union B ...). 
        '''
        from _theorems_ import nonmembershipFolding, binaryNonmembershipFolding
        if len(self.operands) == 2:
            return binaryNonmembershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            return nonmembershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)
