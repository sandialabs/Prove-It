from proveit import Literal, BinaryOperation
from proveit.number.sets import Integers, Reals
from proveit.common import a, b

MOD = Literal(__package__, 'mod', r'~\rm{mod}~')

class Mod(BinaryOperation):
    def __init__(self, dividend, divisor):
        BinaryOperation.__init__(self, MOD, dividend, divisor)
        self.dividend = self.operands[0]
        self.divisor = self.operands[1]

    @classmethod
    def operatorOfOperation(subClass):
        return MOD

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Integers:
            return theorems.modIntClosure
        elif numberSet == Reals:
            return theorems.modRealClosure
    
    def deduceInInterval(self, assumptions=frozenset()):
        from theorems import modInInterval, modInIntervalCO
        from numberSets import deduceInIntegers, deduceInReals
        try:
            # if the operands are integers, then we can deduce that a mod b is in 0..(b-1)
            deduceInIntegers(self.operands, assumptions)
            return modInInterval.specialize({a:self.dividend, b:self.divisor}).checked(assumptions)
        except:
            # if the operands are reals, then we can deduce that a mod b is in [0, b)
            deduceInReals(self.operands, assumptions)
            return modInIntervalCO.specialize({a:self.dividend, b:self.divisor}).checked(assumptions)
