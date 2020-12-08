from proveit import Literal, Operation
from proveit.number.sets import Real, RealPos

class Max(Operation):
    # operator of the Max operation.
    _operator_ = Literal(stringFormat='Max', latexFormat=r'{\rm Max}', theory=__file__)
    
    def __init__(self, *operands):
        Operation.__init__(self, Max._operator_, operands)

    def _closureTheorem(self, numberSet):
        from . import theorems
        if numberSet == Real:
            return theorems.maxRealClosure
        elif numberSet == RealPos:
            return theorems.maxRealPosClosure               
