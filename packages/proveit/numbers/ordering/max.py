from proveit import (equality_prover, Literal, ExprRange, Function,
                     relation_prover, UnsatisfiedPrerequisites)
from proveit.numbers import (
        deduce_number_set, merge_list_of_sets, NumberOperation, Real)
from proveit import a, b, m, n, x, y, S


class Max(NumberOperation, Function):
    # operator of the Max operation.
    _operator_ = Literal(
        string_format='Max',
        latex_format=r'{\rm Max}',
        theory=__file__)

    def __init__(self, *operands, styles=None):
        NumberOperation.__init__(self, Max._operator_, operands, styles=styles)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        For the unary case, where self = Max(a), deduce and return

            [Max(a) = a].

        For the binary case, where self = Max(a, b), deduce and return 

            [Max(a, b)] = [ a if a >= b,
                            b if b >  a ].

        For the more general case (without an ExprRange), deduce and
        return

            [Max(a_1, a_2, ..., a_m, b)] =
             Max(Max(a_1, a_2, ..., a_{m}), b)

        For the binary case, if the conditions in the conditional fxn
        definition are known, then the Max.shallow_simplification()
        method may automatically further evaluate or simplify the rhs.
        If such further reduction is not desired, include
        auto_simplify=False as an argument.
        For the general case with an ExprRange in the arguments, the
        results are unpredictable.
        '''
        if self.operands.is_single():
            from . import max_def_unary
            _x_sub = self.operand
            return max_def_unary.instantiate({x: _x_sub})
        elif self.operands.is_double():
            from . import max_def_bin
            _x_sub = self.operands[0]
            _y_sub = self.operands[1]
            return max_def_bin.instantiate({x: _x_sub, y: _y_sub})
        else:
            from . import max_def_multi
            _a_sub = self.operands[0:-1]
            _b_sub = self.operands[-1]
            _m_sub = _a_sub.num_elements()
            return max_def_multi.instantiate(
                    {m: _m_sub, a: _a_sub, b: _b_sub})

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False, **defaults_config):
        '''
        Returns a proven simplification equation for this Max
        expression assuming the operand(s) has/have been simplified
        and assuming the operand(s) is/are Real.
        For the simple unary case Max(a), returns the proven
        simplification Max(a) = a.
        For the simple binary case Max(a, b), returns a proven
        simplification equation for this Max expression assuming the
        operands 'a' and 'b' have been simplified and that we know or
        have assumed that either a >= b or b > a.
        For the more general case Max(a_1, a_2, ..., a_m, b), returns a
        proven simplification equation of the form
        self = Max(Max(a_1, a_2, ..., a_m), b), where the nested Max()
        call might then be further simplified.
        For the binary case, if the requisite relational knowledge
        among arguments is not to be had, we simply return the equation
        of the Max expression with itself.
        Cases involving ExprRanges are not currently handled, instead
        simply returning the proven judgment |- self=self.
        '''
        from proveit.logic import Equals
        from proveit.numbers import greater_eq

        if self.operands.is_single():
            from . import max_def_unary
            _x_sub = self.operand
            return max_def_unary.instantiate({x: _x_sub})

        # If binary and we know how operands 'a' and 'b' are related ...
        elif self.operands.is_double():
            from proveit.numbers.ordering import max_def_bin
            op_01, op_02 = self.operands[0], self.operands[1]
            if (greater_eq(op_01, op_02).proven()):
                return max_def_bin.instantiate({x: op_01, y: op_02})
            elif (greater_eq(op_02, op_01).proven()):
                from proveit import TransRelUpdater
                from proveit.numbers.ordering import max_bin_args_commute
                expr = self
                eq = TransRelUpdater(expr) # begins as self = self
                expr = eq.update(max_bin_args_commute.instantiate(
                        {x: op_01, y: op_02}, preserve_all=True))
                # then simplify the rhs only
                expr = eq.update(expr.simplification())
                return eq.relation

        # If multi-argument but no ExprRanges
        elif (not any([isinstance (op, ExprRange) for op in self.operands])):
            from . import max_def_multi
            _a_sub = self.operands[0:-1]
            _b_sub = self.operands[-1]
            _m_sub = _a_sub.num_elements()
            return max_def_multi.instantiate(
                    {m: _m_sub, a: _a_sub, b: _b_sub})

        # Otherwise no simplification.
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
