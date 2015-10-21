from proveit.expression import Literal, STRING, LATEX
from proveit.basiclogic.genericOps import Operation, BinaryOperation
from numberSets import NumberOp, Reals, Integers

pkg = __package__

class Mod(BinaryOperation, NumberOp):
    def __init__(self, dividend, divisor):
        BinaryOperation.__init__(self, MOD, dividend, divisor)
        self.dividend = self.operands[0]
        self.divisor = self.operands[1]

    def _closureTheorem(self, numberSet):
        import integer.theorems
        import real.theorems
        if numberSet == Integers:
            return integer.theorems.modClosure
        elif numberSet == Reals:
            return real.theorems.modClosure

MOD = Literal(pkg, 'MOD', {STRING:'mod', LATEX:r'~\rm{mod}~'}, operationMaker = lambda operands : Mod(*operands))

class ModAbs(Operation, NumberOp):
    def __init__(self, value, divisor):
        Operation.__init__(self, MOD_ABS, [value, divisor])
        self.value = value
        self.divisor = divisor
    
    def formatted(self, formatType, fence=False):
        if formatType == STRING:
            return '|'+self.value.formatted(formatType, fence=fence)+'|_{mod ' + self.divisor.formatted(formatType, fence=fence) + '}'
        elif formatType == LATEX:
            return r'\left|'+self.value.formatted(formatType, fence=fence)+r'\right|_{{\rm mod}~' + self.divisor.formatted(formatType, fence=fence) + '}'

    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Reals:
            return real.theorems.modAbsClosure

MOD_ABS = Literal(pkg, 'MOD_ABS', operationMaker = lambda operands : ModAbs(*operands))
