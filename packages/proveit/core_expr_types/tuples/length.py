from proveit import (Expression, Lambda, Operation, Literal, safeDummyVar,
                     singleOrCompositeExpression, ExprTuple,
                     ExprRange, InnerExpr, defaults, USE_DEFAULTS)
from proveit._common_ import a, b, c, d, e, f, g, h, i, j, k, n, x, y

class Len(Operation):
    # operator of the Length operation.
    _operator_ = Literal(stringFormat='length', context=__file__)   
    
    def __init__(self, operand):
        '''
        Len takes a single operand which should properly be an
        ExprTuple or an expression (such as a variable) that
        represents a tuple.
        '''
        operand = singleOrCompositeExpression(operand)
        if isinstance(operand, ExprTuple):
            # Nest an ExprTuple operand in an extra ExprTuple as
            # a clear indication that Len has a single operand
            # that is an ExprTuple rather than multiple operands.
            operand = ExprTuple(operand)
        # In order to always recognize that Len only takes a single
        # operand, we must wrap it as an ExprTuple with one entry.
        Operation.__init__(self, Len._operator_, operand)
    
    @staticmethod
    def extractInitArgValue(argName, operator_or_operators, operand_or_operands):
        if argName=='operand':
            if isinstance(operand_or_operands, ExprTuple):
                return operand_or_operands[0]
            else:
                return operand_or_operands
        
    def string(self, **kwargs):
        return '|' + self.operand.string() + '|'
    
    def latex(self, **kwargs):
        return '|' + self.operand.latex() + '|'
    
    def computation(self, assumptions=USE_DEFAULTS, simplify=True):
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
        # Calling 'replaced' with no repl_map will just perform
        # automatic reductions (if enabled).
        reduced_operand = self.operand.replaced({})
        # Don't auto-reduce ExprRanges on the left side if
        # 'self' is not reduced itself.
        disable_range_reduction = (reduced_operand != self.operand)
        return self._tested_equivalence(
                self._computation, assumptions,
                disable_range_reduction=disable_range_reduction,
                simplify=simplify)
    
    def _computation(self, assumptions=USE_DEFAULTS, must_evaluate=False):
        # Currently not doing anything with must_evaluate
        # What it should do is make sure it evaluates to a number
        # and can circumvent any attempt that will not evaluate to
        # number.
        from proveit.number import zero, one
        if not isinstance(self.operand, ExprTuple):
            # Don't know how to compute the length if the operand is
            # not a tuple. For example, it could be a variable that
            # represent a tuple.  So just return the self equality.
            from proveit.logic import Equals
            return Equals(self, self).prove()
        entries = self.operand
        has_range = any(isinstance(entry, ExprRange) for entry in entries)
        if (len(entries)==1 and has_range 
                and not isinstance(entries[0].body, ExprRange)):
            # Compute the length of a single range.  Examples:
            # |(f(1), ..., f(n))| = n
            # |(f(i), ..., f(j))| = j-i+1
            range_entry = entries[0]
            start_index = range_entry.start_index
            end_index = range_entry.end_index
            lambda_map = range_entry.lambda_map
            if start_index==one:
                from proveit.core_expr_types.tuples._theorems_ import \
                    range_from1_len
                return range_from1_len.instantiate(
                        {f:lambda_map, i:end_index}, assumptions=assumptions)
            else:
                from proveit.core_expr_types.tuples._theorems_ import range_len
                return range_len.instantiate(
                        {f:lambda_map, i:start_index, j:end_index},
                        assumptions=assumptions)
        elif not has_range:
            # Case of all non-range entries.
            if len(entries) == 0:
                # zero length.
                from proveit.core_expr_types.tuples._axioms_ import tuple_len_0
                return tuple_len_0
            elif len(entries) < 10:
                # Automatically get the count and equivalence with
                # the length of the proper iteration starting from
                # 1.  For example,
                # |(a, b, c)| = 3
                # |(a, b, c)| = |(1, .., 3)|
                import proveit.number.numeral.deci
                _n = len(entries)
                len_thm = proveit.number.numeral.deci._theorems_\
                            .__getattr__('tuple_len_%d'%_n)
                repl_map = dict()
                for param, entry in zip(len_thm.explicitInstanceParams(),
                                        entries):
                    repl_map[param] = entry
                return len_thm.specialize(repl_map)
            else:
                #raise NotImplementedError("Can't handle length computation "
                 #                        ">= 10 for %s"%self)
                from proveit.core_expr_types.tuples._axioms_ import tuple_len_incr
                from proveit.number import num
                from proveit.logic import Equals

                eq = tuple_len_incr.instantiate({i: num(len(entries) - 1), a: entries[:-1], b: entries[-1]},
                                                 assumptions=assumptions)

                rhs_simp = eq.rhs._integerBinaryEval(assumptions=assumptions)

                return rhs_simp.subRightSideInto(eq, assumptions=assumptions)
                #return Equals(eq.lhs, eq.rhs._integerBinaryEval(assumptions=assumptions).rhs).prove(assumptions=assumptions)
                #raise NotImplementedError("Can't handle length computation "
                 #                         ">= 10 for %s"%self)
        elif (len(entries)==2 and not isinstance(entries[1], ExprRange)
                and not isinstance(entries[0].body, ExprRange)):
            # Case of an extended range:
            # |(a_1, ..., a_n, b| = n+1 
            from proveit.core_expr_types.tuples._theorems_ import \
                extended_range_len, extended_range_from1_len
            assert isinstance(entries[0], ExprRange)
            range_lambda = entries[0].lambda_map
            range_start = entries[0].start_index
            range_end = entries[0].end_index
            if range_start==one:
                return extended_range_from1_len.instantiate(
                        {f:range_lambda, b:entries[1], i:range_end},
                        assumptions=assumptions)
            else:
                return extended_range_len.instantiate(
                        {f:range_lambda, b:entries[1], 
                         i:range_start, j:range_end},
                        assumptions=assumptions)
        else:
            # Handle the general cases via general_len_val,
            # len_of_ranges_with_repeated_indices,
            # len_of_ranges_with_repeated_indices_from_1,
            # or len_of_empty_range_of_range
            from proveit.core_expr_types.tuples._theorems_ import (
                    general_len, len_of_ranges_with_repeated_indices,
                    len_of_ranges_with_repeated_indices_from_1,
                    len_of_empty_range_of_ranges)
            _x = safeDummyVar(self)

            def entry_map(entry):
                if isinstance(entry, ExprRange):
                    if isinstance(entry.body, ExprRange):
                        # Return an ExprRange of lambda maps.
                        return ExprRange(entry.parameter, 
                                         entry.body.lambda_map,
                                         entry.start_index,
                                         entry.end_index)
                    else:
                        # Use the ExprRange entry's map.
                        return entry.lambda_map
                # For individual elements, just map to the 
                # elemental entry.
                return Lambda(_x, entry)

            def entry_start(entry):
                if isinstance(entry, ExprRange): 
                    if isinstance(entry.body, ExprRange):
                        # Return an ExprRange of lambda maps.
                        return ExprRange(entry.parameter, 
                                         entry.body.start_index,
                                         entry.start_index,
                                         entry.end_index)
                    else:
                        return entry.start_index
                return one  # for individual elements, use start=end=1

            def entry_end(entry):
                if isinstance(entry, ExprRange): 
                    if isinstance(entry.body, ExprRange):
                        # Return an ExprRange of lambda maps.
                        return ExprRange(entry.parameter, 
                                         entry.body.end_index,
                                         entry.start_index,
                                         entry.end_index)
                    else:
                        return entry.end_index
                return one  # for individual elements, use start=end=1

            def empty_range(_i, _j, _f, assumptions):
                # If the start and end are literal ints and form an
                # empty range, then it should be straightforward to
                # prove that the range is empty.
                from proveit.number import isLiteralInt, Add
                from proveit.logic import Equals
                from proveit._common_ import m
                _m = entries[0].start_index
                _n = entries[0].end_index
                empty_req = Equals(Add(_n, one), _m)
                if isLiteralInt(_m) and isLiteralInt(_n):
                    if _n.asInt() + 1 == _m.asInt():
                        empty_req.prove()
                if empty_req.proven(assumptions):
                    _f = Lambda((entries[0].parameter, entries[0].body.parameter), entries[0].body.body)
                    _i = [entry_map(entry) for entry in _i]
                    _j = [entry_map(entry) for entry in _j]
                    return len_of_empty_range_of_ranges.instantiate(
                        {m: _m, n: _n, f: _f, i: _i, j: _j}, assumptions=assumptions)

            _f = [entry_map(entry) for entry in entries]
            _i = [entry_start(entry) for entry in entries]
            _j = [entry_end(entry) for entry in entries]
            _n = Len(_i).computed(assumptions=assumptions, simplify=False)

            from proveit.number import isLiteralInt
            if len(entries)==1 and isinstance(entries[0], ExprRange):
                if isLiteralInt(entries[0].start_index) and isLiteralInt(entries[0].end_index):
                    if entries[0].end_index.asInt() + 1 == entries[0].start_index.asInt():
                        return empty_range(_i, _j, _f, assumptions)

            if all(_==_i[0] for _ in _i) and all(_==_j[0] for _ in _j):
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
                        return thm.instantiate(
                                {n:_n, f:_f, i:_j[0]},
                                assumptions=assumptions)
                    else:
                        thm = len_of_ranges_with_repeated_indices
                        return thm.instantiate(
                                {n:_n, f:_f, i:_i[0], j:_j[0]}, 
                                assumptions=assumptions)

            return general_len.instantiate(
                       {n:_n, f:_f, i:_i, j:_j}, assumptions=assumptions)
    
    def typical_equiv(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to prove that this Len expression is equal to
        something of the form |(i, ..., j)|.
        More generally, use "deduceEquality" (which calls this
        method when it can).
        Examples of handled cases:
            |(a, b, c)| = |(1, ..., 3)|
            |(x_i, ..., x_j)| = |i, ..., j|
        These are typically useful equivalences for proving matching
        length requirements when instantiating a range of parameters.
        '''
        return self._tested_equivalence(self._typical_equiv, assumptions,
                                        simplify=False)
    
    def _typical_equiv(self, assumptions=USE_DEFAULTS):        
        from proveit.number import one
        if not isinstance(self.operand, ExprTuple):
            raise ValueError("Len.typical_equiv may only be performed "
                             "on a Len operating on an ExprTuple, not %s"
                             %self)

        entries = self.operand
        if (len(entries)==1  and isinstance(entries[0], ExprRange) and
                not isinstance(entries[0].body, ExprRange)):
            # Treat the special case something of the form
            # |(f(i), ..., f(j))}.  For example:
            # |(f(i), ..., f(j)| = (i, ..., j)
            range_entry = entries[0]
            start_index = range_entry.start_index
            end_index = range_entry.end_index
            lambda_map = range_entry.lambda_map
            if start_index==one:
                from proveit.core_expr_types.tuples._theorems_ import \
                    range_from1_len_typical_equiv
                return range_from1_len_typical_equiv.instantiate(
                        {f:lambda_map, i:end_index}, assumptions=assumptions)
            else:
                from proveit.core_expr_types.tuples._theorems_ import \
                    range_len_typical_equiv
                return range_len_typical_equiv.instantiate(
                        {f:lambda_map, i:start_index, j:end_index},
                        assumptions=assumptions)
        elif not any(isinstance(entry, ExprRange) for entry in entries):
            if len(entries)==0:
                from proveit.core_expr_types.tuples._theorems_ import \
                    tuple_len_0_typical_equiv
                return tuple_len_0_typical_equiv
            elif len(entries) < 10:
                # Get a "typical equivalence" for the case when there
                # are no ExprRange's.  For example,
                # |(a, b, c)| = |(1, .., 3)|
                import proveit.number.numeral.deci
                n = len(entries)
                equiv_thm = proveit.number.numeral.deci._theorems_\
                                .__getattr__('tuple_len_%d_typical_equiv'%n)
                repl_map = dict()
                for param, entry in zip(equiv_thm.explicitInstanceParams(),
                                        entries):
                    repl_map[param] = entry
                return equiv_thm.instantiate(repl_map)
        elif (len(entries)==2 and not isinstance(entries[1], ExprRange)
                and not isinstance(entries[0].body, ExprRange)):
            # Case of an extended range:
            # |(a_1, ..., a_n, b| = n+1 
            from proveit.core_expr_types.tuples._theorems_ import \
                (extended_range_len_typical_equiv, 
                 extended_range_from1_len_typical_equiv)
            assert isinstance(entries[0], ExprRange)
            range_lambda = entries[0].lambda_map
            range_start = entries[0].start_index
            range_end = entries[0].end_index
            if range_start==one:
                return extended_range_from1_len_typical_equiv.instantiate(
                        {f:range_lambda, b:entries[1], i:range_end},
                        assumptions=assumptions)
            else:
                return extended_range_len_typical_equiv.instantiate(
                        {f:range_lambda, b:entries[1], 
                         i:range_start, j:range_end},
                        assumptions=assumptions)                    
        raise NotImplementedError("Len.typical_equiv not implemented for "
                                  "this case: %s.  Try Len.deduceEquality "
                                  "instead."%self)

    def _tested_equivalence(self, equivalence_fn, assumptions=USE_DEFAULTS,
                            simplify=True, disable_range_reduction=True):
        '''
        Execute a function to get an equivalence, making sure that the
        result is a proper equivalence, a Judgment for an
        Equals expression with the lhs being self.  If
        disable_range_reduction, then disable range reduction while
        deriving the equivalence to ensure it does not get reduced to
        a different form.
        '''
        from proveit import Judgment
        from proveit.logic import Equals
        was_range_reduction_disabled = (
                ExprRange in defaults.disabled_auto_reduction_types)
        try:
            if disable_range_reduction:
                # Disalbe ExprRange reduction while applying the
                # equivalence function (to make sure the right side
                # is not reduced).
                defaults.disabled_auto_reduction_types.add(ExprRange)
            equiv = equivalence_fn(assumptions)
        finally:
            # Restore 'defaults'.
            if disable_range_reduction and not was_range_reduction_disabled:
                defaults.disabled_auto_reduction_types.remove(ExprRange)
        if simplify:
            equiv = equiv.innerExpr().rhs.simplify(assumptions=assumptions)
        assert isinstance(equiv, Judgment)
        assert isinstance(equiv.expr, Equals)
        assert equiv.lhs==self, ("%s differs from %s"%(equiv.lhs, self))
        return equiv
    
    def deduceEquality(self, equality, assumptions=USE_DEFAULTS, 
                       minimal_automation=False):
        from proveit.logic import Equals
        if not isinstance(equality, Equals):
            raise ValueError("The 'equality' should be an Equals expression")        
        if equality.lhs != self:
            raise ValueError("The left side of 'equality' should be 'self'")
        # Try a special-case "typical equivalence".
        if isinstance(equality.rhs, Len):
            if (isinstance(equality.rhs.operand, ExprTuple)
                    and isinstance(self.operand, ExprTuple)):
                if (len(equality.rhs.operand) == 1 and 
                        isinstance(equality.rhs.operand[0], ExprRange)):
                    try:
                        equiv = \
                            self.typical_equiv(assumptions=assumptions)
                        if equiv.expr==equality:
                            return equiv
                    except (NotImplementedError, ValueError):
                        pass
        
        # Next try to compute each side, simplify each side, and
        # prove they are equal.
        lhs_computation = equality.lhs.computation(assumptions=assumptions)
        if isinstance(equality.rhs, Len):
            # Compute both lengths and see if we can prove that they
            # are equal.
            rhs_computation = equality.rhs.computation(assumptions=assumptions)
            eq = Equals(lhs_computation.rhs, rhs_computation.rhs)
            if eq.lhs==eq.rhs:
                # Trivial reflection -- automation is okay for that.
                eq = eq.prove()
            else:
                eq = eq.prove(assumptions, automation=not minimal_automation)
            return Equals.applyTransitivities(
                    [lhs_computation, eq, rhs_computation],
                    assumptions=assumptions)
        else:
            # Compute the lhs length and see if we can prove that it is
            # equal to the rhs.
            eq = Equals(lhs_computation.rhs, equality.rhs)
            if eq.lhs == eq.rhs:
                # Trivial reflection -- automation is okay for that.
                eq = eq.prove()
            else:
                eq = eq.prove(assumptions, automation=not minimal_automation)
            return lhs_computation.applyTransitivity(
                    eq, assumptions=assumptions)
    
    def simplification(self, assumptions=USE_DEFAULTS, automation=True):
        if not automation:
            return Expression.simplification(self, assumptions, automation=False)
        from proveit.relation import TransRelUpdater
        eq = TransRelUpdater(self, assumptions)
        expr = eq.update(self.computation(assumptions))
        expr = eq.update(expr.simplification(assumptions))
        return eq.relation
    
    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        from proveit.core_expr_types.tuples._theorems_ import (
                range_len_in_nats, range_from1_len_in_nats)
        from proveit.number import Naturals, one
        operand = self.operand
        if number_set == Naturals:
            if len(operand)==1 and isinstance(operand[0], ExprRange):
                # Special case of proving that the length
                # of a single range is in the set of Naturals.
                range_start = operand[0].start_index
                range_end = operand[0].end_index   
                range_lambda = operand[0].lambda_map
                if range_start == one:
                    return range_from1_len_in_nats.instantiate(
                            {f:range_lambda, i:range_end},
                            assumptions=assumptions)
                else:
                    return range_len_in_nats.instantiate(
                            {f:range_lambda, i:range_start, j:range_end},
                            assumptions=assumptions)
    
    def doReducedSimplification(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        A simplification of a Len operation computes the length as a sum
        of the lengths of each item of the ExprTuple operand, returning
        the equivalence between the Len expression and this computation,
        simplified to the extent possible.  An item may be a singular element
        (contribution 1 to the length) or an iteration contributing its length.
        '''
        return self._computation(must_evaluate=False, assumptions=assumptions)
    
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Return the evaluation of the length which equates that Len expression
        to an irreducible result.
        '''
        return self._computation(must_evaluate=True, assumptions=assumptions)
    
# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(Len, 'computation', 'computed', 'compute')