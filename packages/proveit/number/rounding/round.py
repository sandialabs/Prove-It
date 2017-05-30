from proveit import Literal, Operation
from proveit.number.sets import Integers, Naturals

class Round(Operation):
    # operator of the Round operation.
    _operator_ = Literal(stringFormat='round', context=__file__)
    
    def __init__(self, A):
        Operation.__init__(self, Round._operator_, A)
        self.operand = A

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Naturals:
            return theorems.roundRealPosClosure
        elif numberSet == Integers:
            return theorems.roundRealClosure
            
