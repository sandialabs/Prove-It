from proveit.expression import Literal, STRING, LATEX
from proveit.basiclogic.genericOps import BinaryOperation
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
