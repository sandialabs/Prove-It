from proveit import Literal, Function, relation_prover
from proveit.numbers import (
        deduce_number_set, merge_list_of_sets, NumberOperation, Real)
from proveit import a, n, K


class Max(NumberOperation, Function):
    # operator of the Max operation.
    _operator_ = Literal(
        string_format='Max',
        latex_format=r'{\rm Max}',
        theory=__file__)

    def __init__(self, *operands, styles=None):
        NumberOperation.__init__(self, Max._operator_, operands, styles=styles)

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Deduce that the Max(a_1, ..., a_n) expression produces a
        value in number_set. This will depend on the Max arguments
        a_1, ..., a_n all being known or assumed to be subsets of some
        superset number_set.
        deduce_in_number_set() is also called from deduce_number_set(),
        which first works to find some minimal standard number set
        that includes the number sets deduced for each argument.
        '''
        from . import max_set_closure
        if number_set in max_set_closure.condition.domain.elements:
            _K_sub = number_set
            _a_sub = self.operands
            _n_sub = _a_sub.num_elements()
            return max_set_closure.instantiate(
                    {K: _K_sub, n: _n_sub, a: _a_sub})
        else:
            raise NotImplementedError(
                    "Max.deduce_in_number_set() method was called with "
                    "number_set = {0}, but the method has not yet been "
                    "implemented for that number_set.".
                    format(number_set))

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most
        restrictive standard number set we can readily know.
        After deriving a candidate super set that contains the
        number set deduced for each argument, the fxn then calls
        the self.deduce_in_number_set() fxn defined above.
        '''
        list_of_operand_sets = []
        # find a minimal std number set for operand
        for operand in self.operands:
            operand_ns = deduce_number_set(operand).domain
            list_of_operand_sets.append(operand_ns)
        # merge the resulting list of std number sets into a
        # single superset, if possible
        minimal_super_set = merge_list_of_sets(list_of_operand_sets)
        return self.deduce_in_number_set(minimal_super_set)
