from proveit import (equality_prover, Literal, Function, relation_prover,
                      UnsatisfiedPrerequisites)
from proveit.numbers import (
        deduce_number_set, merge_list_of_sets, NumberOperation, Real)
from proveit import a, n, S


class Max(NumberOperation, Function):
    # operator of the Max operation.
    _operator_ = Literal(
        string_format='Max',
        latex_format=r'{\rm Max}',
        theory=__file__)

    def __init__(self, *operands, styles=None):
        NumberOperation.__init__(self, Max._operator_, operands, styles=styles)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False, **defaults_config):
        '''
        For the simple binary case Max(a, b), returns a proven
        simplification equation for this Max expression assuming the
        operands 'a' and 'b' have been simplified and that we know or
        have assumed that either a >= b or b > a. If such relational
        knowledge is not to be had, we simply return the equation of
        the Max expression with itself.
        Cases with more than 2 operands are not yet handled.
        '''
        from proveit.logic import Equals
        from proveit.numbers import greater_eq

        # We're only set up to deal with binary operator version
        if not self.operands.is_double():
            # Default is no simplification if not a binary operation.
            return Equals(self, self).prove()

        # If binary and we know how operands 'a' and 'b' are related ...
        op_01, op_02 = self.operands[0], self.operands[1]
        if (greater_eq(op_01, op_02).proven()
            or greater_eq(op_02, op_01).proven()):
            from proveit import x, y
            from proveit.numbers.ordering import max_def_bin
            return max_def_bin.instantiate({x: op_01, y: op_02})

        # Otherwise still no simplification.
        return Equals(self, self).prove()

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
        _S_sub = number_set
        _a_sub = self.operands
        _n_sub = _a_sub.num_elements()

        try:
            return max_set_closure.instantiate(
                    {S: _S_sub, n: _n_sub, a: _a_sub})
        except Exception as the_exception:
            raise ValueError(
                    "Something went wrong in Max.deduce_in_number_set(), "
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
