from proveit import Literal, Operation
from proveit.number.sets import Reals, RealsPos

class Min(Operation):
    # operator of the Min operation.
    _operator_ = Literal(stringFormat='Min', latexFormat=r'{\rm Min}', context=__file__)
    
    def __init__(self, A, B):
        Operation.__init__(self, Min._operator_, [A, B])

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.minRealClosure
        elif numberSet == RealsPos:
            return theorems.minRealPosClosure            

