from proveit import Literal, Operation
from proveit.number.sets import Integers, Reals
from proveit._common_ import a, b

class Mod(Operation):
    # operator of the Mod operation.
    _operator_ = Literal(stringFormat='mod ', latexFormat=r'~\textup{mod}~',
                         context=__file__)
    
    def __init__(self, dividend, divisor):
        Operation.__init__(self, Mod._operator_, (dividend, divisor))
        self.dividend = self.operands[0]
        self.divisor = self.operands[1]

    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Integers:
            return theorems.modIntClosure
        elif numberSet == Reals:
            return theorems.modRealClosure
    
    def deduceInInterval(self, assumptions=frozenset()):
        from .theorems import modInInterval, modInIntervalCO
        from numberSets import deduceInIntegers, deduceInReals
        try:
            # if the operands are integers, then we can deduce that a mod b is in 0..(b-1)
            deduceInIntegers(self.operands, assumptions)
            return modInInterval.specialize({a:self.dividend, b:self.divisor}).checked(assumptions)
        except:
            # if the operands are reals, then we can deduce that a mod b is in [0, b)
            deduceInReals(self.operands, assumptions)
            return modInIntervalCO.specialize({a:self.dividend, b:self.divisor}).checked(assumptions)
