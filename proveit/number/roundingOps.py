from proveit.expression import Operation, Literal, LATEX

pkg = __package__

class Floor(Operation):
    def __init__(self, A):
        Operation.__init__(self, FLOOR, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\lfloor ' + self.operand.formatted(formatType, fence=False) + r'\rfloor'
        return Operation.formatted(self, formatType, fence)

FLOOR = Literal(pkg, 'FLOOR', operationMaker = lambda operands : Floor(*operands))

class Ceil(Operation):
    def __init__(self, A):
        Operation.__init__(self, FLOOR, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\lceil ' + self.operand.formatted(formatType, fence=False) + r'\rceil'
        return Operation.formatted(self, formatType, fence)

CEIL = Literal(pkg, 'CEIL', operationMaker = lambda operands : Ceil(*operands))
