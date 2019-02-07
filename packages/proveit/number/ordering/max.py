from proveit import Literal, Operation
from proveit.number.sets import Reals, RealsPos

class Max(Operation):
    # operator of the Max operation.
    _operator_ = Literal(stringFormat='Max', latexFormat=r'{\rm Max}', context=__file__)
    
    def __init__(self, *operands):
        Operation.__init__(self, Max._operator_, operands)

    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Reals:
            return theorems.maxRealClosure
        elif numberSet == RealsPos:
            return theorems.maxRealPosClosure               
