from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import x, A, B


class Difference(Operation):
    # operator of the Difference operation
    _operator_ = Literal(string_format='-', theory=__file__)

    def __init__(self, A, B):
        Operation.__init__(self, Difference._operator_, [A, B])

    def membership_equivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element in (A - B)] = [(element in A) and (element not in B)
        where self = (A - B).
        '''
        from ._axioms_ import difference_def
        return difference_def.instantiate(
            {x: element, A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def nonmembership_equivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element not in (A - B)] = [(element not in A) or (element in B)]
        where self = (A - B).
        '''
        from ._theorems_ import nonmembership_equiv
        return nonmembership_equiv.instantiate(
            {x: element, A: self.operands[0], B: self.operands[1]})

    def unfold_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A - B)], derive and return [(element in A) and (element not in B)],
        where self represents (A - B).
        '''
        from ._axioms_ import difference_def
        return difference_def.instantiate(
            {x: element, A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def deduce_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in A] and [element not in B], derive and return [element in (A - B)],
        where self represents (A - B).
        '''
        from ._theorems_ import membership_folding
        return membership_folding.instantiate(
            {x: element, A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def deduce_nonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From either [element not in A] or [element in B], derive and return [element not in (A - B)],
        where self represents (A - B).
        '''
        from ._theorems_ import nonmembership_folding
        return nonmembership_folding.instantiate(
            {x: element, A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
