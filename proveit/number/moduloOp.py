from proveit.expression import Literal, STRING, LATEX
from proveit.basiclogic.genericOps import Operation, BinaryOperation
from numberSets import NumberOp, Reals, Integers
from proveit.common import a, b

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
    
    def deduceInInterval(self, assumptions=frozenset()):
        import integer.theorems
        import real.theorems
        from numberSets import deduceInIntegers, deduceInReals
        try:
            # if the operands are integers, then we can deduce that a mod b is in 0..(b-1)
            deduceInIntegers(self.operands, assumptions)
            return integer.theorems.modInInterval.specialize({a:self.dividend, b:self.divisor}).checked(assumptions)
        except:
            # if the operands are reals, then we can deduce that a mod b is in [0, b)
            deduceInReals(self.operands, assumptions)
            return real.theorems.modInIntervalCO.specialize({a:self.dividend, b:self.divisor}).checked(assumptions)
        

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
