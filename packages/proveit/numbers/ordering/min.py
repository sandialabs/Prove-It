from proveit import Literal, Function
from proveit.numbers.number_sets import Real, RealPos

class Min(Function):
    # operator of the Min operation.
    _operator_ = Literal(stringFormat='Min', latexFormat=r'{\rm Min}', theory=__file__)
    
    def __init__(self, *operands):
        Function.__init__(self, Min._operator_, operands)

    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Real:
            return theorems.minRealClosure
        elif numberSet == RealPos:
            return theorems.minRealPosClosure            

