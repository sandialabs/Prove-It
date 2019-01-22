from proveit import Literal, Function
from proveit.number.sets import Reals, RealsPos

class Min(Function):
    # operator of the Min operation.
    _operator_ = Literal(stringFormat='Min', latexFormat=r'{\rm Min}', context=__file__)
    
    def __init__(self, *operands):
        Function.__init__(self, Min._operator_, operands)

    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Reals:
            return theorems.minRealClosure
        elif numberSet == RealsPos:
            return theorems.minRealPosClosure            

