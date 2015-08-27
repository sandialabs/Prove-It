from proveit.expression import Literal, STRING, LATEX
from proveit.basiclogic.genericOps import BinaryOperation

pkg = __package__

class Mod(BinaryOperation):
    def __init__(self, dividend, divisor):
        BinaryOperation.__init__(self, MOD, dividend, divisor)
        self.dividend = self.operands[0]
        self.divisor = self.operands[1]

MOD = Literal(pkg, 'MOD', {STRING:'mod', LATEX:r'~\rm{mod}~'}, operationMaker = lambda operands : Mod(*operands))
