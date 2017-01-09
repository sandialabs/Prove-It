from proveit import Literal, Operation
from proveit.number.sets import Reals, RealsPos

MIN = Literal(__package__, 'Min', r'{\rm Min}')

class Min(Operation):
    def __init__(self, A, B):
        Operation.__init__(self, MIN, [A, B])

    @classmethod
    def operatorOfOperation(subClass):
        return MIN
    
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.minRealClosure
        elif numberSet == RealsPos:
            return theorems.minRealPosClosure            

