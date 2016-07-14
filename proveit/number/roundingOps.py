from proveit import Operation, Literal
from numberSets import NumberOp, Integers

pkg = __package__

class Floor(Operation, NumberOp):
    def __init__(self, A):
        Operation.__init__(self, FLOOR, A)
        self.operand = A

    @classmethod
    def operatorOfOperation(subClass):
        return FLOOR
    
    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Integers:
            return real.theorems.floorClosure
            
    def latex(self, **kwargs):
        return r'\lfloor ' + self.operand.latex(fence=False) + r'\rfloor'
        
FLOOR = Literal(pkg, 'Floor')

class Ceil(Operation, NumberOp):
    def __init__(self, A):
        Operation.__init__(self, CEIL, A)
        self.operand = A

    @classmethod
    def operatorOfOperation(subClass):
        return CEIL
    
    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Integers:
            return real.theorems.ceilClosure

    def latex(self, **kwargs):
        return r'\lceil ' + self.operand.latex(fence=False) + r'\rceil'
    
CEIL = Literal(pkg, 'Ceil')

class Round(Operation, NumberOp):
    def __init__(self, A):
        Operation.__init__(self, ROUND, A)
        self.operand = A

    @classmethod
    def operatorOfOperation(subClass):
        return ROUND
        
    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Integers:
            return real.theorems.roundClosure
            
ROUND = Literal(pkg, 'Round', '{\rm Round}')
