from proveit import Literal, Operation
from proveit.number.sets import Integers, Naturals

class Floor(Operation):
    # operator of the Floor operation.
    _operator_ = Literal(stringFormat='floor', context=__file__)
    
    def __init__(self, A):
        Operation.__init__(self, Floor._operator_, A)
        self.operand = A

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Naturals:
            return theorems.floorRealPosClosure
        elif numberSet == Integers:
            return theorems.floorRealClosure
            
    def latex(self, **kwargs):
        return r'\lfloor ' + self.operand.latex(fence=False) + r'\rfloor'
        
