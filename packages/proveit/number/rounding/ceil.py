from proveit import Literal, Function
from proveit.number.sets import Integers, NaturalsPos

class Ceil(Function):
    # operator of the Ceil operation.
    _operator_ = Literal(stringFormat='ceil', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Ceil._operator_, A)
        # self.operand = A # check later that the operand attribute
        # is still working!

    def _closureTheorem(self, numberSet):
        from . import _theorems_
        if numberSet == NaturalsPos:
            return _theorems_.ceilRealPosClosure
        elif numberSet == Integers:
            return _theorems_.ceilRealClosure

    def latex(self, **kwargs):
        return r'\lceil ' + self.operand.latex(fence=False) + r'\rceil'
    
