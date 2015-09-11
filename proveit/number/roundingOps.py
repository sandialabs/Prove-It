from proveit.expression import Operation, Literal, LATEX
from numberSets import NumberOp, Integers

pkg = __package__

class Floor(Operation, NumberOp):
    def __init__(self, A):
        Operation.__init__(self, FLOOR, A)
        self.operand = A

    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Integers:
            return real.theorems.floorClosure
            
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\lfloor ' + self.operand.formatted(formatType, fence=False) + r'\rfloor'
        return Operation.formatted(self, formatType, fence)

FLOOR = Literal(pkg, 'FLOOR', operationMaker = lambda operands : Floor(*operands))

class Ceil(Operation, NumberOp):
    def __init__(self, A):
        Operation.__init__(self, FLOOR, A)
        self.operand = A

    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Integers:
            return real.theorems.ceilClosure
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\lceil ' + self.operand.formatted(formatType, fence=False) + r'\rceil'
        return Operation.formatted(self, formatType, fence)

CEIL = Literal(pkg, 'CEIL', operationMaker = lambda operands : Ceil(*operands))

class Round(Operation, NumberOp):
    def __init__(self, A):
        Operation.__init__(self, ROUND, A)
        self.operand = A
    
    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Integers:
            return real.theorems.roundClosure
            
ROUND = Literal(pkg, 'Round', {LATEX:r'{\rm Round}'}, operationMaker = lambda operands : Round(*operands))
