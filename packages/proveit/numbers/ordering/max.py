from proveit import Literal, Operation
from proveit.numbers.number_sets import Real, RealPos


class Max(Operation):
    # operator of the Max operation.
    _operator_ = Literal(
        string_format='Max',
        latex_format=r'{\rm Max}',
        theory=__file__)

    def __init__(self, *operands):
        Operation.__init__(self, Max._operator_, operands)

    def _closureTheorem(self, number_set):
        from . import theorems
        if number_set == Real:
            return theorems.max_real_closure
        elif number_set == RealPos:
            return theorems.max_real_pos_closure
