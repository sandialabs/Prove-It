from proveit import (Expression, Lambda, Operation, Literal, safe_dummy_var,
                     single_or_composite_expression, ExprTuple,
                     ExprRange, InnerExpr, defaults,
                     equality_prover, prover)
from proveit import a, b, c, d, e, f, g, h, i, j, k, n, x, y


class Len(Operation):
    # operator of the Length operation.
    _operator_ = Literal(string_format='length', theory=__file__)

    def __init__(self, operands, *, styles=None):
        '''
        Len can take an explicit ExprTuple as operands, or
        it may take an expression (such as a varaible) that
        represents a tuple.  Either way, this expression is
        taken as the 'operands'.
        '''
        if isinstance(operands, ExprRange):
            # An ExprRange cannot represent an ExprTuple,
            # so we must want this wrapped in an ExprTuple.
            operands = ExprTuple(operands)
        # In order to always recognize that Len only takes a single
        # operand, we must wrap it as an ExprTuple with one entry.
        Operation.__init__(self, Len._operator_, operands=operands, styles=styles)

    @staticmethod
    def extract_init_arg_value(arg_name, operator, operands):
        if arg_name == 'operands':
            return operands

    def string(self, **kwargs):
        return '|' + self.operands.string() + '|'

    def latex(self, **kwargs):
        return '|' + self.operands.latex() + '|'

    @equality_prover('computed', 'compute')
    def computation(self, **defaults_config):
        '''
        Compute this Len expression, returning the equality
        between self and the expression for its computed value.
        Examples:
            |(a, b, c)| = 3
            |(x_1, ..., x_n, y)| = n+1
            |(f(i), ..., f(j), x_1, ..., x_n)| = (j-i+1) + (n-1+1)
            |x| = |x|
        In the last case, the 'x' represents an unknown tuple,
        so there is not anything we can do to compute it.
        '''
        # Currently not doing anything with must_evaluate
        # What it should do is make sure it evaluates to a number
        # and can circumvent any attempt that will not evaluate to
        # number.
        from proveit.numbers import one
        #print(self.operands.entries[0].__class__)
        if not isinstance(self.operands, ExprTuple):
            # Don't know how to compute the length if the operand is
            # not a tuple. For example, it could be a variable that
            # represent a tuple.  So just return the self equality.
            from proveit.logic import Equals
            return Equals(self, self).conclude_via_reflexivity()
        entries = self.operands.entries
        has_range = any(isinstance(entry, ExprRange) for entry in entries)
        if (len(entries) == 1 and has_range
                and not isinstance(entries[0].body, ExprRange)):
            # Compute the length of a single range.  Examples:
            # |(f(1), ..., f(n))| = n
            # |(f(i), ..., f(j))| = j-i+1
            range_entry = entries[0]
            start_index = range_entry.true_start_index
            end_index = range_entry.true_end_index
            lambda_map = range_entry.lambda_map
            if start_index == one:
                from proveit.core_expr_types.tuples import range_from1_len
                len_comp = range_from1_len.instantiate(
                    {f: lambda_map, i: end_index}, auto_simplify=False)
            else:
                from proveit.core_expr_types.tuples import range_len
                len_comp = range_len.instantiate(
                    {f: lambda_map, i: start_index, j: end_index}, auto_simplify=False)
        elif not has_range:
            # Case of all non-range entries.
            if len(entries) == 0:
                # zero length.
                from proveit.core_expr_types.tuples import tuple_len_0
                return tuple_len_0
            elif len(entries) < 10:
                # Automatically get the count and equality with
                # the length of the proper iteration starting from
                # 1.  For example,
                # |(a, b, c)| = 3
                # |(a, b, c)| = |(1, .., 3)|
                import proveit.numbers.numerals.decimals
                _n = len(entries)
                len_thm = proveit.numbers.numerals.decimals\
                    .__getattr__('tuple_len_%d' % _n)
                repl_map = dict()
                for param, entry in zip(len_thm.explicit_instance_params(),
                                        entries):
                    repl_map[param] = entry
                return len_thm.instantiate(repl_map, auto_simplify=False)
            else:
                # raise NotImplementedError("Can't handle length computation "
                #                        ">= 10 for %s"%self)
                from proveit.core_expr_types.tuples import tuple_len_incr
                from proveit.numbers import num
                from proveit.logic import Equals
                # We turn on automation because this length equality should
                # be true (we know the number of elements is equal to the 
                # number of entries since there are no ExprRange entries).
                # Since we know it's true, why not commit ourselves to 
                # proving it?
                return tuple_len_incr.instantiate(
                    {i: num(len(entries) - 1), a: entries[:-1], b: entries[-1]},
                    automation=True)
                # return Equals(eq.lhs, eq.rhs._integerBinaryEval(assumptions=assumptions).rhs).prove(assumptions=assumptions)
                # raise NotImplementedError("Can't handle length computation "
                #                         ">= 10 for %s"%self)
        elif (len(entries) == 2 and not isinstance(entries[1], ExprRange)
                and not isinstance(entries[0].body, ExprRange)):
            # Case of an extended range:
            # |(a_1, ..., a_n, b| = n+1
            from proveit.core_expr_types.tuples import \
                extended_range_len, extended_range_from1_len
            assert isinstance(entries[0], ExprRange)
            range_lambda = entries[0].lambda_map
            range_start = entries[0].true_start_index
            range_end = entries[0].true_end_index
            if range_start == one:
                len_comp = extended_range_from1_len.instantiate(
                    {f: range_lambda, x: entries[1], i: range_end})
            else:
                len_comp = extended_range_len.instantiate(
                    {f: range_lambda, x:entries[1], 
                     i: range_start, j: range_end})
        else:
            # Handle the general cases via general_len_val,
            # len_of_ranges_with_repeated_indices,
            # len_of_ranges_with_repeated_indices_from_1,
            # or len_of_empty_range_of_range
            from proveit.core_expr_types.tuples import (
                general_len, len_of_ranges_with_repeated_indices,
                len_of_ranges_with_repeated_indices_from_1,
                len_of_empty_range_of_ranges)
            _x = safe_dummy_var(self)
            preserved_exprs = defaults.preserved_exprs

            def entry_map(entry):
                # Don't auto-simplify the entry.
                preserved_exprs.add(entry)
                if isinstance(entry, ExprRange):
                    if isinstance(entry.body, ExprRange):
                        # Return an ExprRange of lambda maps.
                        return ExprRange(entry.parameter,
                                         entry.body.lambda_map,
                                         entry.true_start_index,
                                         entry.true_end_index)
                    else:
                        return entry.lambda_map
                # For individual elements, just map to the
                # elemental entry.
                return Lambda(_x, entry)

            def entry_start(entry):
                if isinstance(entry, ExprRange):
                    if isinstance(entry.body, ExprRange):
                        # Return an ExprRange of lambda maps.
                        return ExprRange(entry.parameter,
                                         entry.body.true_start_index,
                                         entry.true_start_index,
                                         entry.true_end_index)
                    else:
                        return entry.true_start_index
                return one  # for individual elements, use start=end=1

            def entry_end(entry):
                if isinstance(entry, ExprRange):
                    if isinstance(entry.body, ExprRange):
                        # Return an ExprRange of lambda maps.
                        return ExprRange(entry.parameter,
                                         entry.body.true_end_index,
                                         entry.true_start_index,
                                         entry.true_end_index)
                    else:
                        return entry.true_end_index
                return one  # for individual elements, use start=end=1

            def empty_range(_i, _j, _f):
                # If the start and end are literal ints and form an
                # empty range, then it should be straightforward to
                # prove that the range is empty.
                from proveit.numbers import is_numeric_int, Add
                from proveit.logic import Equals
                from proveit import m
                _m = entries[0].true_start_index
                _n = entries[0].true_end_index
                empty_req = Equals(Add(_n, one), _m)
                if is_numeric_int(_m) and is_numeric_int(_n):
                    if _n.as_int() + 1 == _m.as_int():
                        empty_req.prove()
                if empty_req.proven():
                    _f = Lambda(
                        (entries[0].parameter,
                         entries[0].body.parameter),
                        entries[0].body.body)
                    _i = entry_map(_i)
                    _j = entry_map(_j)
                    return len_of_empty_range_of_ranges.instantiate(
                        {m: _m, n: _n, f: _f, i: _i, j: _j}).with_wrapping_at()

            _f = [entry_map(entry) for entry in entries]
            _i = [entry_start(entry) for entry in entries]
            _j = [entry_end(entry) for entry in entries]
            _n = Len(_i).computed()

            from proveit.numbers import is_numeric_int
            if len(entries) == 1 and isinstance(entries[0], ExprRange):
                if (is_numeric_int(entries[0].true_start_index) and 
                        is_numeric_int(entries[0].true_end_index)):
                    if (entries[0].true_end_index.as_int() + 1 
                            == entries[0].true_start_index.as_int()):
                        return empty_range(_i[0], _j[0], _f)

            len_comp = None
            if all(_ == _i[0] for _ in _i) and all(_ == _j[0] for _ in _j):
                if isinstance(_i[0], ExprRange):
                    if _i[0].is_parameter_independent:
                        # A parameter independent range means they
                        # are all the same.
                        _i = [_i[0].body]
                if isinstance(_j[0], ExprRange):
                    if _j[0].is_parameter_independent:
                        # A parameter independent range means they
                        # are all the same.
                        _j = [_j[0].body]
                if (not isinstance(_i[0], ExprRange) and
                        not isinstance(_j[0], ExprRange)):
                    # special cases where the indices are repeated
                    if _i[0] == one:
                        thm = len_of_ranges_with_repeated_indices_from_1
                        len_comp = thm.instantiate(
                            {n: _n, f: _f, i: _j[0]}).with_wrapping_at()
                    else:
                        thm = len_of_ranges_with_repeated_indices
                        len_comp = thm.instantiate(
                            {n: _n, f: _f, 
                             i: _i[0], j: _j[0]}).with_wrapping_at()
            if len_comp is None:
                len_comp = general_len.instantiate(
                    {n: _n, f: _f, i: _i, j: _j}, 
                    preserved_exprs=preserved_exprs).with_wrapping_at()
                if not defaults.auto_simplify and len_comp.lhs != self:
                    # Make sure the left side is reduced to the
                    # original expression (self) which is preserved.
                    return len_comp.inner_expr().lhs.shallow_simplify(
                        preserved_exprs=preserved_exprs)
        if defaults.auto_simplify:
            # Ensure the right side is simplified which may have
            # been prevented due to automatic preservation of
            # instatiation expressions.
            return len_comp.inner_expr().rhs.simplify()
        return len_comp


    @equality_prover('typical_form', 'typify')
    def typical_eq(self, **defaults_config):
        '''
        Attempt to prove that this Len expression is equal to
        something of the form |(i, ..., j)|.
        More generally, use "deduce_equal" (which calls this
        method when it can).
        Examples of handled cases:
            |(a, b, c)| = |(1, ..., 3)|
            |(x_i, ..., x_j)| = |i, ..., j|
        These are typically useful equalities for proving matching
        length requirements when instantiating a range of parameters.
        '''
        from proveit.numbers import one
        if not isinstance(self.operands, ExprTuple):
            raise ValueError("Len.typical_eq may only be performed "
                             "on a Len operating on an ExprTuple, not %s"
                             % self)

        entries = self.operands.entries
        if (len(entries) == 1 and isinstance(entries[0], ExprRange) and
                not isinstance(entries[0].body, ExprRange)):
            # Treat the special case something of the form
            # |(f(i), ..., f(j))}.  For example:
            # |(f(i), ..., f(j)| = (i, ..., j)
            range_entry = entries[0]
            start_index = range_entry.true_start_index
            end_index = range_entry.true_end_index
            lambda_map = range_entry.lambda_map
            if start_index == one:
                from proveit.core_expr_types.tuples import \
                    range_from1_len_typical_eq
                return range_from1_len_typical_eq.instantiate(
                    {f: lambda_map, i: end_index}, auto_simplify=False)
            else:
                from proveit.core_expr_types.tuples import \
                    range_len_typical_eq
                return range_len_typical_eq.instantiate(
                    {f: lambda_map, i: start_index, j: end_index},
                    auto_simplify=False)
        elif not any(isinstance(entry, ExprRange) for entry in entries):
            if len(entries) == 0:
                from proveit.core_expr_types.tuples import \
                    tuple_len_0_typical_eq
                return tuple_len_0_typical_eq
            elif len(entries) < 10:
                # Get a "typical equality" for the case when there
                # are no ExprRange's.  For example,
                # |(a, b, c)| = |(1, .., 3)|
                import proveit.numbers.numerals.decimals
                n = len(entries)
                eq_thm = proveit.numbers.numerals.decimals\
                                .__getattr__('tuple_len_%d_typical_eq' % n)
                repl_map = dict()
                for param, entry in zip(eq_thm.explicit_instance_params(),
                                        entries):
                    repl_map[param] = entry
                return eq_thm.instantiate(repl_map, auto_simplify=False)
        elif (len(entries) == 2 and not isinstance(entries[1], ExprRange)
                and not isinstance(entries[0].body, ExprRange)):
            # Case of an extended range:
            # |(a_1, ..., a_n, b| = |(1, ..., n_1)|
            from proveit.core_expr_types.tuples import \
                (extended_range_len_typical_eq,
                 extended_range_from1_len_typical_eq)
            assert isinstance(entries[0], ExprRange)
            range_lambda = entries[0].lambda_map
            range_start = entries[0].true_start_index
            range_end = entries[0].true_end_index
            if range_start == one:
                return extended_range_from1_len_typical_eq.instantiate(
                    {f: range_lambda, x: entries[1], i: range_end},
                    auto_simplify=False)
            else:
                return extended_range_len_typical_eq.instantiate(
                    {f: range_lambda, x: entries[1],
                     i: range_start, j: range_end}, auto_simplify=False)
        raise NotImplementedError("Len.typical_eq not implemented for "
                                  "this case: %s.  Try Len.deduce_equal "
                                  "instead." % self)

    def readily_equal(self, rhs):
        '''
        ToDo: treat some simple cases as readily provable.
        '''
        return False

    @equality_prover('equated', 'equate')
    def deduce_equal(self, rhs, **defaults_config):
        '''
        Prove the given equality with self on the left-hand side.
        '''
        from proveit.logic import Equals
        equality = Equals(self, rhs)
        if equality.proven():
            return equality.prove() # Already proven.
        lhs = self
        with defaults.temporary() as temp_defaults:
            # Auto-simplify everything except the left and right sides
            # of the equality.
            temp_defaults.preserved_exprs={lhs, rhs}
            temp_defaults.auto_simplify=True

            # Try a special-case "typical equality".
            if isinstance(rhs, Len):
                if (isinstance(rhs.operands, ExprTuple)
                        and isinstance(self.operands, ExprTuple)):
                    if (rhs.operands.num_entries() == 1 and
                            isinstance(rhs.operands[0], ExprRange)):
                        try:
                            eq = self.typical_eq()
                            if eq.expr == equality:
                                return eq
                        except (NotImplementedError, ValueError):
                            pass
    
            # Next try to compute each side, simplify each side, and
            # prove they are equal.
            lhs_computation = lhs.computation()
            if isinstance(rhs, Len):
                # Compute both lengths and see if we can prove that they
                # are equal.
                rhs_computation = rhs.computation()
                eq = Equals(lhs_computation.rhs, rhs_computation.rhs)
                if eq.lhs == eq.rhs:
                    # Trivial reflection
                    eq = eq.conclude_via_reflexivity()
                else:
                    # eq = eq.conclude_via_transitivity()
                    eq = eq.prove() # will use canonical forms
                return Equals.apply_transitivities(
                    [lhs_computation, eq, rhs_computation])
            else:
                # Compute the lhs length and see if we can prove that it is
                # equal to the rhs.
                eq = Equals(lhs_computation.rhs, rhs)
                if eq.lhs == eq.rhs:
                    # Trivial reflection
                    eq = eq.conclude_via_reflexivity()
                else:
                    eq = eq.conclude_via_transitivity()
                return lhs_computation.apply_transitivity(eq)

    @equality_prover('evaluated', 'evaluate')
    def evaluation(self, **defaults_config):
        '''
        Returns a proven evaluations equation for this Len
        expression assuming.  Performs the "computation" of the
        Len expression and then evaluates the right side.
        
        Note: simplifying the operand, when it is an ExprTuple,
        is not so important when evaluating its length.
        '''
        computation = self.computation()
        return computation.inner_expr().rhs.evaluate()

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Len
        expression assuming.  Performs the "computation" of the
        Len expression and then simplifies the right side.
        '''
        if must_evaluate:
            return self.computation(auto_simplify=True)
        else:
            return Operation.shallow_simplification(self)


    def readily_provable_number_set(self):
        '''
        The length should be a natural number.
        '''
        from proveit.numbers import Natural
        return Natural

    @prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        from proveit.core_expr_types.tuples import (
            range_len_is_nat, range_from1_len_is_nat)
        from proveit.logic import InSet
        from proveit.numbers import Natural, one
        operands = self.operands
        if number_set == Natural:
            if (operands.num_entries() == 1
                    and isinstance(operands[0], ExprRange)):
                # Special case of proving that the length
                # of a single range is in the set of Natural numbers.
                range_start = operands[0].true_start_index
                range_end = operands[0].true_end_index
                range_lambda = operands[0].lambda_map
                if range_start == one:
                    return range_from1_len_is_nat.instantiate(
                        {f: range_lambda, i: range_end})
                else:
                    return range_len_is_nat.instantiate(
                        {f: range_lambda, i: range_start, j: range_end})
        # Otherwise, prove the number set through computation.
        computation = self.computation()
        InSet(computation.rhs, number_set).prove()
        return InSet(self, number_set).prove()

