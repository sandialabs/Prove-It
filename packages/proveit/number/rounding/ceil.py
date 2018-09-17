from proveit import Literal, Function
from proveit.number.sets import Integers, NaturalsPos

class Ceil(Function):
    # operator of the Ceil operation.
    _operator_ = Literal(stringFormat='ceil', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Ceil._operator_, A)
        self.operand = A

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == NaturalsPos:
            return theorems.ceilRealPosClosure
        elif numberSet == Integers:
            return theorems.ceilRealClosure

    def latex(self, **kwargs):
        return r'\lceil ' + self.operand.latex(fence=False) + r'\rceil'
    
