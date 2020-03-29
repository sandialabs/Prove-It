from proveit import Literal, Function
from proveit.number.sets import Integers, Naturals

class Floor(Function):
    # operator of the Floor operation.
    _operator_ = Literal(stringFormat='floor', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Floor._operator_, A)
        # self.operand = A # check later that the operand attribute
        # is still working!

    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Naturals:
            return theorems.floorRealPosClosure
        elif numberSet == Integers:
            return theorems.floorRealClosure
            
    def latex(self, **kwargs):
        return r'\lfloor ' + self.operand.latex(fence=False) + r'\rfloor'
        
