from proveit import Literal, Operation
from proveit.number.set import Integers, NaturalsPos

CEIL = Literal(__package__, 'Ceil')

class Ceil(Operation):
    def __init__(self, A):
        Operation.__init__(self, CEIL, A)
        self.operand = A

    @classmethod
    def operatorOfOperation(subClass):
        return CEIL
    
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == NaturalsPos:
            return theorems.ceilRealPosClosure
        elif numberSet == Integers:
            return theorems.ceilRealClosure

    def latex(self, **kwargs):
        return r'\lceil ' + self.operand.latex(fence=False) + r'\rceil'
    
