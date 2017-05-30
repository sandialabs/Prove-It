from proveit import Literal, BinaryOperation, USE_DEFAULTS
from proveit.common import x, A, B

class Difference(BinaryOperation):
    # operator of the Difference operation
    _operator_ = Literal(stringFormat='-', context=__file__)    

    def __init__(self, A, B):
        BinaryOperation.__init__(self, Difference._operator_, A, B)

    def evaluateMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate [element in (A - B)] to TRUE or FALSE.
        '''
        from _axioms_ import differenceDef
        from proveit.logic import InSet, Equals
        equiv = differenceDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        value = equiv.rhs.evaluate(assumptions=assumptions).rhs
        return Equals(InSet(element, self), value).prove(assumptions)

    def evaluateNonMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate [element in (A - B)] to TRUE or FALSE.
        '''
        from _theorems_ import nonMembershipEval
        from proveit.logic import InSet, Equals
        equiv = nonMembershipEval.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        value = equiv.rhs.evaluate(assumptions=assumptions).rhs
        return equiv(InSet(element, self), value).prove(assumptions)
                        
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A - B)], derive and return [(element in A) and (element not in B)],
        where self represents (A - B). 
        '''
        from _axioms_ import membershipUnfolding
        return membershipUnfolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in A] and [element not in B], derive and return [element in (A - B)],
        where self represents (A - B). 
        '''
        from _axioms_ import membershipFolding
        return membershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deduceNonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From either [element not in A] or [element in B], derive and return [element not in (A - B)],
        where self represents (A - B). 
        '''
        from _axioms_ import nonmembershipFolding
        return nonmembershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        