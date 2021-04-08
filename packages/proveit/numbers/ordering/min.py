from proveit import Literal, Function
from proveit.numbers.number_sets import Real, RealPos


class Min(Function):
    # operator of the Min operation.
    _operator_ = Literal(
        string_format='Min',
        latex_format=r'{\rm Min}',
        theory=__file__)

    def __init__(self, *operands, styles=None):
        Function.__init__(self, Min._operator_, operands, styles=styles)

    def _closureTheorem(self, number_set):
        from . import theorems
        if number_set == Real:
            return theorems.min_real_closure
        elif number_set == RealPos:
            return theorems.min_real_pos_closure
