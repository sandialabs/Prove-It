from proveit import Literal, Operation
from proveit.number.sets import Reals

class ModAbs(Operation):
    # operator of the ModAbs operation.
    _operator_ = Literal(stringFormat='ModAbs', context=__file__)
    
    def __init__(self, value, divisor):
        Operation.__init__(self, ModAbs._operator_, (value, divisor))
        self.value = value
        self.divisor = divisor
        
    def string(self, **kwargs):
        return ( '|' + self.value.string(fence=False)+'|_{mod '
                + self.divisor.string(fence=False)
                + '}')

    def latex(self, **kwargs):
        return (  r'\left|'
                + self.value.string(fence=False)
                + r'\right|_{\textup{mod}~'
                + self.divisor.string(fence=False)
                + '}')

    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Reals:
            return theorems.modAbsRealClosure
