from proveit import Literal, Operation
from proveit.number.set import Integers, Naturals

ROUND = Literal(__package__, 'Round', '{\rm Round}')

class Round(Operation):
    def __init__(self, A):
        Operation.__init__(self, ROUND, A)
        self.operand = A

    @classmethod
    def operatorOfOperation(subClass):
        return ROUND
        
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Naturals:
            return theorems.roundRealPosClosure
        elif numberSet == Integers:
            return theorems.roundRealClosure
            
