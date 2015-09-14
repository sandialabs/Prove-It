from proveit.expression import Operation, Literal, LATEX

pkg = __package__

class Bra(Operation):
    def __init__(self, A):
        Operation.__init__(self, BRA, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\langle ' + self.operand.formatted(formatType, fence=False) + r' \rvert'
        else:
            return '<'+self.operand.formatted(formatType, fence=False)+'|'

BRA = Literal(pkg, 'BRA', operationMaker = lambda operands : Bra(*operands))

class Ket(Operation):
    def __init__(self, A):
        Operation.__init__(self, KET, A)
        self.operand = A
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\lvert ' + self.operand.formatted(formatType, fence=False) + r' \rangle'
        else:
            return '|'+self.operand.formatted(formatType, fence=False)+'>'

KET = Literal(pkg, 'KET', operationMaker = lambda operands : Ket(*operands))

class Meas(Operation):
    def __init__(self, ket):
        Operation.__init__(self, MEAS, ket)
        self.ket = ket
    
MEAS = Literal(pkg, 'MEAS', {LATEX: r'{\cal M}'}, operationMaker = lambda operands : Meas(*operands))

