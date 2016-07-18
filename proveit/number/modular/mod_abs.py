from proveit import Literal, Operation
from proveit.number.set import Reals

MOD_ABS = Literal(__package__, 'MOD_ABS')

class ModAbs(Operation):
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
        import theorems
        if numberSet == Reals:
            return theorems.modAbsRealClosure
