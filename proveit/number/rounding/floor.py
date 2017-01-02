from proveit import Literal, Operation
from proveit.number.sets import Integers, Naturals

FLOOR = Literal(__package__, 'Floor')

class Floor(Operation):
    def __init__(self, A):
        Operation.__init__(self, FLOOR, A)
        self.operand = A

    @classmethod
    def operatorOfOperation(subClass):
        return FLOOR
    
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Naturals:
            return theorems.floorRealPosClosure
        elif numberSet == Integers:
            return theorems.floorRealClosure
            
    def latex(self, **kwargs):
        return r'\lfloor ' + self.operand.latex(fence=False) + r'\rfloor'
        
