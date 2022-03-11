from proveit import Literal, Function, relation_prover
from proveit.numbers import (
        deduce_number_set, merge_list_of_sets, NumberOperation, Real)
from proveit import a, n, S


class Min(NumberOperation, Function):
    # operator of the Min operation.
    _operator_ = Literal(
        string_format='Min',
        latex_format=r'{\rm Min}',
        theory=__file__)

    def __init__(self, *operands, styles=None):
        NumberOperation.__init__(self, Min._operator_, operands, styles=styles)

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Deduce that the Min(a_1, ..., a_n) expression produces a
        value in number_set. This will depend on the Min arguments
        a_1, ..., a_n all being known or assumed to be subsets of some
        superset number_set.
        deduce_in_number_set() is also called from deduce_number_set(),
        which first works to find some minimal standard number set
        that includes the number sets deduced for each argument.
        '''
        from . import min_set_closure
        _S_sub = number_set
        _a_sub = self.operands
        _n_sub = _a_sub.num_elements()

        try:
            return min_set_closure.instantiate(
                    {S: _S_sub, n: _n_sub, a: _a_sub})
        except Exception as the_exception:
            raise ValueError(
                    "Something went wrong in Min.deduce_in_number_set(), "
                    "with the error: {}".
                    format(the_exception))

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

