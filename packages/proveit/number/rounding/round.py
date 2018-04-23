from proveit import Literal, Function
from proveit.number.sets import Integers, Naturals

class Round(Function):
    # operator of the Round operation.
    _operator_ = Literal(stringFormat='round', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Round._operator_, A)
        self.operand = A

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Naturals:
            return theorems.roundRealPosClosure
        elif numberSet == Integers:
            return theorems.roundRealClosure
            
