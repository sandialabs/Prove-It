from proveit import Literal, BinaryOperation, USE_DEFAULTS
from proveit._common_ import x, A, B

class Difference(BinaryOperation):
    # operator of the Difference operation
    _operator_ = Literal(stringFormat='-', context=__file__)    

    def __init__(self, A, B):
        BinaryOperation.__init__(self, Difference._operator_, A, B)

    def membershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element in (A - B)] = [(element in A) and (element not in B)
        where self = (A - B).
        '''
        from _axioms_ import differenceDef
        return differenceDef.specialize({x:element,A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def nonmembershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element not in (A - B)] = [(element not in A) or (element in B)]
        where self = (A - B).
        '''
        from _theorems_ import nonmembershipEquiv
        return nonmembershipEquiv.specialize({x:element, A:self.operands[0], B:self.operands[1]})

    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A - B)], derive and return [(element in A) and (element not in B)],
        where self represents (A - B). 
        '''
        from _axioms_ import differenceDef
        return differenceDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in A] and [element not in B], derive and return [element in (A - B)],
        where self represents (A - B). 
        '''
        from _theorems_ import membershipFolding
        return membershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deduceNonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From either [element not in A] or [element in B], derive and return [element not in (A - B)],
        where self represents (A - B). 
        '''
        from _theorems_ import nonmembershipFolding
        return nonmembershipFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        