from proveit import Literal, Operation
from proveit.number.sets import Reals, RealsPos

MAX = Literal(__package__, 'Max', r'{\rm Max}')

class Max(Operation):
    def __init__(self, A, B):
        Operation.__init__(self, MAX, [A, B])

    @classmethod
    def operatorOfOperation(subClass):
        return MAX

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.maxRealClosure
        elif numberSet == RealsPos:
            return theorems.maxRealPosClosure               
