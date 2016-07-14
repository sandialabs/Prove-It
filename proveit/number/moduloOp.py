from proveit import Literal, Operation, BinaryOperation
from numberSets import NumberOp, Reals, Integers
from proveit.common import a, b

pkg = __package__

class Mod(BinaryOperation, NumberOp):
    def __init__(self, dividend, divisor):
        BinaryOperation.__init__(self, MOD, dividend, divisor)
        self.dividend = self.operands[0]
        self.divisor = self.operands[1]

    @classmethod
    def operatorOfOperation(subClass):
        return MOD

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
        

MOD = Literal(pkg, 'mod', r'~\rm{mod}~')

class ModAbs(Operation, NumberOp):
    def __init__(self, value, divisor):
        Operation.__init__(self, MOD_ABS, [value, divisor])
        self.value = value
        self.divisor = divisor
    
    @classmethod
    def operatorOfOperation(subClass):
        return MOD_ABS
        
    def string(self, **kwargs):
        return '|'+self.value.string(fence=False)+'|_{mod ' + self.divisor.string(fence=False) + '}'

    def latex(self, **kwargs):
        return '\left|'+self.value.string(fence=False)+'\right|_{{\rm mod}~' + self.divisor.string(fence=False) + '\right}'

    def _closureTheorem(self, numberSet):
        import real.theorems
        if numberSet == Reals:
            return real.theorems.modAbsClosure

MOD_ABS = Literal(pkg, 'MOD_ABS')
