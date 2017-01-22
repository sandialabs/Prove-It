from proveit import Literal, AssociativeOperation, USE_DEFAULTS
from proveit.common import x, A, B, Amulti

INTERSECT = Literal(__package__, stringFormat = 'intersection', latexFormat = r'\cap')

class Intersect(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        AssociativeOperation.__init__(self, INTERSECT, *operands)

    @classmethod
    def operatorOfOperation(subClass):
        return INTERSECT  

    def membershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element in (A intersect B ...)] = [(element in A) and (element in B) ...]
        where self = (A intersect B ...).
        '''
        from _axioms_ import intersectDef
        from _theorems_ import membershipEquiv
        if len(self.operands) == 2:       
            return intersectDef.specialize({x:element, A:self.operands[0], B:self.operands[1]})
        else:
            return membershipEquiv.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def nonMembershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element not in (A intersect B ...)] = [(element not in A) or (element not in B) ...]
        where self = (A intersect B ...).
        '''
        from _axioms_ import binaryNonMembershipEquiv
        from _theorems_ import nonMembershipEquiv
        if len(self.operands) == 2:       
            return binaryNonMembershipEquiv.specialize({x:element, A:self.operands[0], B:self.operands[1]})
        else:
            return nonMembershipEquiv.specialize({x:element, Amulti:self.operands})
    
    def evaluateMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate [element in (A intersection B ..)] to TRUE or FALSE.
        '''
        from _axioms_ import intersectionDef
        from _theorems_ import membershipEval
        from proveit.logic import InSet, Equals
        if len(self.operands) == 2:
            equiv = intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            equiv = membershipEval.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)
        value = equiv.rhs.evaluate(assumptions=assumptions).rhs
        return Equals(InSet(element, self), value).prove(assumptions)

    def evaluateNonMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate [element not in (A intersection B ..)] to TRUE or FALSE.
        '''
        from _theorems_ import binaryNonMembershipEval, nonMembershipEval
        from proveit.logic import InSet, Equals
        if len(self.operands) == 2:
            equiv = binaryNonMembershipEval.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            equiv = nonMembershipEval.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)
        value = equiv.rhs.evaluate(assumptions=assumptions).rhs
        return Equals(InSet(element, self), value).prove(assumptions)
                                
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A intersection B ...)], derive and return [(element in A) and (element in B) ...],
        where self represents (A intersection B ...). 
        '''
        from _axioms_ import binaryMembershipUnfolding, membershipUnfolding
        if len(self.operands) == 2:
            return binaryMembershipUnfolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            return membershipUnfolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)
            
    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in A] and [element in B] ..., derive and return [element in (A intersection B ...)],
        where self represents (A intersection B ...). 
        '''
        from _axioms_ import binaryMembershipFolding, membershipFolding
        if len(self.operands) == 2:
            return binaryMembershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:      
            return membershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

    def deduceNonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From either [element not in A] or [element not in B] ..., derive and return [element not in (A intersection B ...)],
        where self represents (A intersection B ...). 
        '''
        from _axioms_ import nonmembershipFolding, binaryNonmembershipFolding
        if len(self.operands) == 2:
            return binaryNonmembershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            return nonmembershipFolding.specialize({x:element, Amulti:self.operands}, assumptions=assumptions)

