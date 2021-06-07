from proveit import Literal, Function, relation_prover
from proveit.numbers.number_sets import Real
from proveit import a, n

class Max(Function):
    # operator of the Max operation.
    _operator_ = Literal(
        string_format='Max',
        latex_format=r'{\rm Max}',
        theory=__file__)

    def __init__(self, *operands, styles=None):
        Function.__init__(self, Max._operator_, operands, styles=styles)

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        from . import max_real_closure
        _a = self.operands
        _n = _a.num_elements()
        if number_set == Real:
            return max_real_closure.instantiate({n:_n, a:_a})
        else:
            raise NotImplementedError(
                    "Max.deduce_in_number_set only implemented for Reals.")
