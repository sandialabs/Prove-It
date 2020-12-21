from proveit import Judgment, Literal, Operation, ExprRange, USE_DEFAULTS, StyleOptions, maybe_fenced_latex, ProofFailure, InnerExpr
from proveit._common_ import a, b, c, d, i, j, k, l, n, x, y
from proveit.logic import Equals
from proveit.logic.irreducible_value import is_irreducible_value
from proveit.numbers.numerals.decimals import DIGITS
import proveit.numbers.numerals.decimals._theorems_
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, group_commutation, pairwise_evaluation
from proveit import TransRelUpdater
import bisect


class Add(Operation):
    # operator of the Add operation
    _operator_ = Literal(string_format='+', theory=__file__)

    # Map terms to sets of Judgment equalities that involve
    # the term on the left hand side.
    known_equalities = dict()

    # Adding two numerals may import a theorem for the evaluation.
    # Track which ones we have encountered already.
    added_numerals = set()

    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        # The default style will be to use subtraction notation (relevant where operands are negated).
        # Call 'with_subtraction_at' to alter this default.
        subtraction_positions = [_k for _k, operand in enumerate(
            operands) if Add._isNegatedOperand(operand)]
        styles = {
            'subtraction_positions': '(' + ' '.join(str(pos) for pos in subtraction_positions) + ')'}
        Operation.__init__(self, Add._operator_, operands, styles=styles)
        self.terms = self.operands

    @staticmethod
    def _isNegatedOperand(operand):
        '''
        Returns True iff the given operand is negated directly or an iteration with a negated body
        '''
        from proveit.numbers import Neg
        return isinstance(
            operand,
            Neg) or (
            isinstance(
                operand,
                ExprRange) and isinstance(
                operand.lambda_map.body,
                Neg))

    def style_options(self):
        # Added by JML on 9/10/19
        options = StyleOptions(self)
        options.add(
            'subtraction_positions',
            "Position(s) to use subtraction notation instead of adding the negation at the specified indices")
        return options

    def with_subtraction_at(self, *subtraction_positions):
        return self.with_styles(
            subtraction_positions='(' +
            ' '.join(
                str(pos) for pos in subtraction_positions) +
            ')')

    def subtraction_positions(self):
        '''
        Return a list of subtraction notation positions according to the current style setting.
        '''
        return [int(pos_str) for pos_str in self.get_style(
            'subtraction_positions').strip('()').split(' ') if pos_str != '']

    def _formatted(self, format_type, **kwargs):
        '''
        Override Operation._formatted so to enable subtraction notation where desired.
        '''
        from proveit import ExprRange
        from proveit.numbers import Neg
        subtraction_positions = self.subtraction_positions()
        if len(subtraction_positions) > 0 and len(self.operands) > 1:
            operators = []
            operands = list(self.operands)
            for operand in operands:
                if isinstance(operand, ExprRange):
                    # Make the operator an ExprRange in correspondence
                    # with the operands ExprRange
                    operators.append(
                        ExprRange(
                            operand.lambda_map.parameter_or_parameters,
                            self.operator,
                            operand.start_index,
                            operand.end_index))
                else:
                    operators.append(self.operator)
            implicit_first_operator = True  # the first operator is implicit if it is a '+'
            for pos in subtraction_positions:
                if pos >= len(operands):
                    continue
                operand = operands[pos]
                if pos == 0:
                    implicit_first_operator = False
                if isinstance(operand, Neg):
                    # format negated operand using subtraction notation
                    operators[pos] = Neg._operator_
                    operands[pos] = operand.operand
                elif isinstance(operand, ExprRange):
                    if isinstance(operand.lambda_map.body, Neg):
                        # format iteration with negation using subtraction
                        # notation
                        operators[pos] = ExprRange(
                            operand.lambda_map.parameter,
                            Neg._operator_,
                            operand.start_index,
                            operand.end_index)
                        operands[pos] = ExprRange(
                            operand.lambda_map.parameter,
                            operand.lambda_map.body.operand,
                            operand.start_index,
                            operand.end_index) .with_styles(
                            **operand.get_styles())
                elif pos == 0:
                    # not negated after all -- revert to the "implicit first
                    # operator" default
                    implicit_first_operator = False
            return Operation._formattedOperation(
                format_type,
                operators,
                operands,
                self.wrap_positions(),
                self.get_style('justification'),
                implicit_first_operator=implicit_first_operator,
                **kwargs)
        else:
            return Operation._formattedOperation(
                format_type,
                self.operator,
                self.operands,
                self.wrap_positions(),
                self.get_style('justification'),
                **kwargs)

    def remake_constructor(self):
        # Added by JML on 9/10/19
        if len(
            self.operands) == 2 and self.subtraction_positions() == (
            1,) and Add._isNegatedOperand(
                self.operands[1]):
            return 'subtract'  # use a different constructor if using the subtraction style
        return Operation.remake_constructor(self)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        from proveit.numbers import Neg
        if len(
            self.operands) == 2 and self.subtraction_positions() == (
            1,) and Add._isNegatedOperand(
                self.operands[1]):
            yield self.operands[0]
            assert isinstance(
                self.operands[1], Neg), "The second operand must be negated"
            yield self.operands[1].operand
        else:
            for operand in self.operands:
                yield operand

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        call_strs = Operation.remake_with_style_calls(self)
        subtraction_positions = self.subtraction_positions()
        default_subtraction_positions = [
            _k for _k, operand in enumerate(
                self.operands) if Add._isNegatedOperand(operand)]
        if subtraction_positions != default_subtraction_positions:
            call_strs.append('with_subtraction_at(' + ','.join(str(pos)
                                                               for pos in subtraction_positions) + ')')
        return call_strs

    def _closureTheorem(self, number_set):
        from ._theorems_ import add_nat_closure, add_real_closure, add_complex_closure, add_int_closure
        from proveit.numbers import Real, Complex, Integer, Natural
        if number_set == Real:
            return add_real_closure
        elif number_set == Complex:
            return add_complex_closure
        elif number_set == Integer:
            return add_int_closure
        elif number_set == Natural:
            return add_nat_closure

    def equality_side_effects(self, judgment):
        '''
        Record the judgment in Add.known_equalities, associated for
        each term.
        '''
        from proveit.numbers import Neg
        if not isinstance(judgment, Judgment):
            raise ValueError("Expecting 'judgment' to be a Judgment.")
        if not isinstance(judgment.expr, Equals):
            raise ValueError("Expecting the judgment to be an equality.")
        addition = judgment.lhs
        if not isinstance(addition, Add):
            raise ValueError(
                "Expecting lhs of judgment to be of an Add expression.")

        if is_irreducible_value(judgment.rhs):
            for term in addition.terms:
                # print("adding known equalities:", term)
                Add.known_equalities.setdefault(term, set()).add(judgment)

            if len(addition.terms) == 2:
                # deduce the commutation form: b+a=c from a+b=c
                if addition.terms[0] != addition.terms[1]:
                    yield (lambda assumptions: judgment.inner_expr().lhs.commute(0, 1, assumptions))

                if all(not isinstance(term, Neg) for term in addition.terms):
                    # From a+b=c
                    # deduce the negations form: -a-b=-c
                    #      the subtraction form: c-b=a
                    #      and the reversed subtraction form: b-c = -a
                    yield (lambda assumptions: self.deduce_negation(judgment.rhs, assumptions))
                    yield (lambda assumptions: self.deduce_subtraction(judgment.rhs, assumptions))
                    yield (lambda assumptions: self.deduce_reversed_subtraction(judgment.rhs, assumptions))

    def deduce_strict_inc_add(self, x, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19. renamed by WMW 9/6/19.

        '''
        from ._theorems_ import strictly_increasing_additions
        from proveit.numbers import num
        # print(b)
        for _i, term in enumerate(self.terms):
            if term == x:
                idx = _i
        _i = num(idx)
        _j = num(len(self.terms) - 1 - idx)
        _a = self.terms[:idx]
        _b = self.terms[idx]
        _c = self.terms[idx + 1:]
        # print(strictly_increasing_additions.instantiate({m:num(idx),n:num(n_val),AA:self.terms[:idx],B:self.terms[idx],CC:self.terms[idx+1:]}, assumptions=assumptions))
        return strictly_increasing_additions.instantiate(
            {i: _i, j: _j, a: _a, b: _b, c: _c}, assumptions=assumptions)

    def deduce_strict_dec_add(self, x, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19. renamed by WMW 9/6/19.

        '''
        from ._theorems_ import strictly_decreasing_additions
        from proveit.numbers import num
        # print(b)
        # print(self.terms)
        for _i, term in enumerate(self.terms):
            if term == x:
                idx = _i
        _i = num(idx)
        _j = num(len(self.terms) - 1 - idx)
        _a = self.terms[:idx]
        _b = self.terms[idx]
        _c = self.terms[idx + 1:]        # print(n_val)
        return strictly_decreasing_additions.instantiate(
            {i: _i, j: _j, a: _a, b: _b, c: _c}, assumptions=assumptions)

    def deduce_negation(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return -(a-b) = -rhs
        '''
        from proveit.numbers.addition.subtraction._theorems_ import negated_add
        if len(self.terms) != 2:
            raise Exception(
                "deduce_negation implemented only when there are two and only two added terms")
        deduction = negated_add.instantiate(
            {a: self.terms[0], b: self.terms[1], c: rhs}, assumptions=assumptions)
        return deduction

    def deduce_subtraction(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return rhs - b = a.
        '''
        from proveit.numbers.addition.subtraction._theorems_ import subtract_from_add
        if len(self.terms) != 2:
            raise Exception(
                "deduce_subtraction implemented only when there are two and only two added terms")
        deduction = subtract_from_add.instantiate(
            {a: self.terms[0], b: self.terms[1], c: rhs}, assumptions=assumptions)
        return deduction

    def deduce_reversed_subtraction(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return b - rhs = -a.
        '''
        from proveit.numbers.addition.subtraction._theorems_ import subtract_from_add_reversed
        if len(self.terms) != 2:
            raise Exception(
                "subtract_from_add_reversed implemented only when there are two and only two added terms")
        deduction = subtract_from_add_reversed.instantiate(
            {a: self.terms[0], b: self.terms[1], c: rhs}, assumptions=assumptions)
        return deduction

    def conversion_to_multiplication(self, assumptions=USE_DEFAULTS):
        '''
        From the addition of the same values, derive and return
        the equivalence as a multiplication. For example,
        a + a + a = 3 * a
        '''
        from proveit import ExprRange
        from proveit.numbers import one
        from proveit.numbers.multiplication._theorems_ import (
            mult_def_rev, repeated_addition_to_mult)
        if not all(operand == self.operands[0] for operand in self.operands):
            raise ValueError(
                "'as_mult' is only applicable on an 'Add' expression if all operands are the same: %s" %
                str(self))
        if (len(self.operands) == 1 and isinstance(self.operands[0], ExprRange)
                and self.operands[0].is_parameter_independent
                and self.operands[0].start_index == one):
            expr_range = self.operands[0]
            return repeated_addition_to_mult.instantiate(
                {x: expr_range.body, n: expr_range.end_index},
                assumptions=assumptions)
        _n = self.operands.length(assumptions)
        _a = self.operands
        _x = self.operands[1]
        return mult_def_rev.instantiate({n: _n, a: _a, x: _x},
                                        assumptions=assumptions)

    def cancelations(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        all simple cancellations are performed (where there are exact
        negations that occur).
        '''
        from proveit.numbers import Neg
        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        neg_operand_indices = dict()
        for _i, operand in enumerate(self.operands):
            if isinstance(operand, Neg):
                neg_operand_indices.setdefault(operand.operand, set()).add(_i)

        canceled_indices = []
        for _i, operand in enumerate(self.operands):
            if isinstance(operand, Neg):
                continue
            if operand in neg_operand_indices:
                indices = neg_operand_indices[operand]
                _j = indices.pop()
                if len(indices) == 0:
                    # no more indices to use in the future
                    neg_operand_indices.pop(operand)
                # By finding where i and j will be inserted into the canceled_indices
                # array, we can figure out how much they need to shift by to compensate
                # for previous cancelations.
                i_shift = bisect.bisect_left(canceled_indices, _i)
                j_shift = bisect.bisect_left(canceled_indices, _j)
                # insert the last one first so we don't need to compensate:
                if _i < _j:
                    canceled_indices.insert(j_shift, _j)
                    canceled_indices.insert(i_shift, _i)
                else:
                    canceled_indices.insert(i_shift, _i)
                    canceled_indices.insert(j_shift, _j)
                expr = eq.update(expr.cancelation(_i - i_shift, _j - j_shift,
                                                  assumptions))
        return eq.relation

    def cancelation(self, idx1, idx2, assumptions=USE_DEFAULTS):
        '''
        Attempt a simple cancelation between operands at index i and j.
        If one of these operands is the negation of the other, deduce
        and return an equality between self and a form in which these
        operands are canceled.
        '''
        from .subtraction._theorems_ import add_cancel_basic, add_cancel_reverse, add_cancel_general, add_cancel_general_rev
        from .subtraction._theorems_ import add_cancel_triple_12, add_cancel_triple_13, add_cancel_triple_23
        from .subtraction._theorems_ import add_cancel_triple_21, add_cancel_triple_31, add_cancel_triple_32
        from proveit.numbers import num, Neg
        if idx1 > idx2:
            # choose i to be less than j
            return self.cancelation(idx2, idx1, assumptions)

        if Neg(self.operands[idx1]) == self.operands[idx2]:
            basic_thm = add_cancel_basic
            triple_thms = (
                add_cancel_triple_12,
                add_cancel_triple_13,
                add_cancel_triple_23)
            general_thm = add_cancel_general
            canceled_op = self.operands[idx1]
        elif self.operands[idx1] == Neg(self.operands[idx2]):
            basic_thm = add_cancel_reverse
            triple_thms = (
                add_cancel_triple_21,
                add_cancel_triple_31,
                add_cancel_triple_32)
            general_thm = add_cancel_general_rev
            canceled_op = self.operands[idx2]
        else:
            raise ValueError("Unable to cancel operands idx1 and idx2; "
                             "one is not the negation of the other.")

        if len(self.operands) == 2:
            return basic_thm.instantiate(
                {a: canceled_op}, assumptions=assumptions)
        elif len(self.operands) == 3:
            # _k is the 3rd index, completing i and j in the set {0,1,2}.
            _k = {0, 1, 2}.difference([idx1, idx2]).pop()
            thm = triple_thms[2 - _k]
            return thm.instantiate({a: canceled_op, b: self.operands[_k]},
                                   assumptions=assumptions)
        else:
            _a = self.operands[:idx1]
            _b = canceled_op
            _c = self.operands[idx1 + 1:idx2]
            _d = self.operands[idx2 + 1:]
            _i = num(len(_a))
            _j = num(len(_c))
            _k = num(len(_d))
            spec = general_thm.instantiate(
                {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c, d: _d},
                assumptions=assumptions)
            # set the proper subtraction styles to match the original
            sub_positions = self.subtraction_positions()
            spec.inner_expr().lhs.with_subtraction_at(*sub_positions)
            def update_pos(p): return p if p < idx1 else (
                p - 1 if p < idx2 else p - 2)
            spec.inner_expr().rhs.with_subtraction_at(
                *[update_pos(p) for p in sub_positions])
            return spec

    def zero_eliminations(self, assumptions=USE_DEFAULTS):
        '''
        Derive and return this Add expression equal to a form in which
        all zero's are eliminated.
        '''
        from proveit.numbers import zero

        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands)):
            if operand == zero:
                idx = len(self.operands) - rev_idx - 1
                expr = eq.update(expr.zero_elimination(idx, assumptions))
                if not isinstance(expr, Add):
                    # can't do an elimination if reduced to a single term.
                    break

        return eq.relation

    def zero_elimination(self, idx, assumptions=USE_DEFAULTS):
        '''
        Derive and return this Add expression equal to a form in which
        a specific zero operand (at the given index) is eliminated.
        '''
        from proveit.numbers import zero, num
        from ._theorems_ import elim_zero_left, elim_zero_right, elim_zero_any

        if self.operands[idx] != zero:
            raise ValueError(
                "Operand at the index %d expected to be zero for %s" %
                (idx, str(self)))

        if len(self.operands) == 2:
            if idx == 0:
                return elim_zero_left.instantiate(
                    {a: self.operands[1]}, assumptions=assumptions)
            else:
                return elim_zero_right.instantiate(
                    {a: self.operands[0]}, assumptions=assumptions)
        _a = self.operands[:idx]
        _b = self.operands[idx + 1:]
        _i = num(len(_a))
        _j = num(len(_b))
        return elim_zero_any.instantiate(
            {i: _i, j: _j, a: _a, b: _b}, assumptions=assumptions)

    def deduce_zero_from_neg_self(self, assumptions=USE_DEFAULTS):
        '''
        added by JML on 9/10/19. renamed by WMW on 9/6/19.
        Given x + (-x) return x.
        '''
        from ._theorems_ import add_neg_self
        from proveit.numbers import Neg
        if len(self.operands) != 2:
            raise IndexError(
                "Expecting two operands.  Use substitution and inner_expr() for more than two operands")
        if isinstance(self.operands[0], Neg):
            if self.operands[0].operand != self.operands[1]:
                raise ValueError(
                    "Expecting one value to be the negation of the other")
        elif isinstance(self.operands[1], Neg):
            if self.operands[0] != self.operands[1].operand:
                raise ValueError(
                    "Expecting one value to be the negation of the other")
        else:
            raise ValueError("Expecting at least one value to be negated")
        return add_neg_self.instantiate(
            {x: self.terms[0]}, assumptions=assumptions)
    """
    def derive_expanded_neg_self(self, idx=0, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/26/19
        given an expression with a term that is a negation of itself cancel them out
        a + b + (-b) + c = a + c
        '''
        from ._theorems_ import expanded_add_neg_self
        from proveit.numbers import Neg, num
        expr = self
        # print("self, idx in add_neg_self", expr, idx)
        if len(expr.operands) ==2:
            # the simple binary case
            return expr.derive_zero_from_neg_self(assumptions)

        if idx < 0 or idx > len(expr.operands) - 1:
            raise IndexError("Index must be between 0 and %s"%str(len(expr.operands)-1))
        if not isinstance(expr.operands[idx], Neg):
            raise ValueError("Expecting value at %s to be negated"%str(idx))

        if idx != len(expr.operands) - 1 and expr.operands[idx + 1] == expr.operands[idx].operand:
            one = expr.operands[idx].operand
            two = expr.operands[idx + 1]
            one_idx = idx
            two_idx = idx + 1
        elif idx != 0 and expr.operands[idx - 1] == expr.operands[idx].operand:
            one = expr.operands[idx - 1]
            two = expr.operands[idx].operand
            one_idx = idx - 1
            two_idx = idx
        else:
            raise ValueError("Expecting a value next to %s to be equal to %s"%(str(expr.operands[idx]), str(expr.operands[idx].operand)))

        return expanded_add_neg_self.instantiate({m:num(one_idx),n:num(len(expr.operands)-1-two_idx), AA:expr.operands[:one_idx], y:one, x:two, BB:expr.operands[two_idx + 1:]}, assumptions=assumptions)
    """

    def _createDict(self, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/24/19
        Creates a dictionary from an addition expression where the keys are common terms and values
        are the indices where they occur.  Also returns the order of initial occurrence for each
        type of term.
        JML had, at my (WMW) suggestion, had positive terms come before negative terms.  This was
        working fine but I removed this feature because it isn't clear that it is always desirable
        and may be better to mess with the order minimally.
        '''
        from proveit.numbers import one, Neg, Mult, Numeral

        hold = {}
        order = []

        for _i, val in enumerate(self.operands):
            # loop through each operand

            # used to differentiate positive and negative for ordering
            if isinstance(val, Neg):
                # place it in the correct place regardless of negation
                val = val.operand
            elif isinstance(val, Mult):
                # use the last factor to determine what is a "like" term
                val = val.operands[-1]
            if isinstance(
                val,
                Numeral) or (
                is_irreducible_value(val) and not isinstance(
                    val,
                    Literal)):
                # Group together all basic numbers (numerals, numeral sequences, and decimals),
                # using 1 as a representative.
                # But exclude special number constants like e, i, or pi which are Irreducible Literals.
                # Those should be grouped together.
                val = one

            # either create a new key or put in an existing key
            if val in hold:
                # if the key exists, just add the value to the list
                hold[val].append(_i)
            else:
                # if not, create the key and add the value
                hold[val] = [_i]
                order.append(val)

        # See if we can expand the "terms" to be combined to
        # include more factors.
        for _k, val in enumerate(order):
            if val == one:
                continue
            if isinstance(val, Neg) and val in hold:
                continue  # positive and negatives are handled together when possible
            # start with the most expanded and widdle down as needed
            newval = self.operands[hold[val][0]]
            if isinstance(newval, Neg):
                newval = newval.operand  # overlook the negation at the moment
            for _i in hold[val][1:]:
                operand = self.operands[_i]
                if isinstance(operand, Neg):
                    operand = operand.operand  # overlook the negation
                while newval != operand:
                    try:
                        if isinstance(operand, Mult):
                            operand.index(newval)
                            # newval is contained as a factor in the operand,
                            # so keep it as is for now.
                            break
                    except ValueError:
                        pass
                    assert isinstance(newval, Mult), "This is unexpected"
                    if len(newval.operands) > 2:
                        newval = Mult(newval.operands[1:])
                    else:
                        newval = newval.operands[-1]
            if isinstance(val, Neg):
                newval = Neg(newval)  # put the negation back
            if newval != val:
                # replace the "term" with an expanded term
                hold[newval] = hold[val]
                del hold[val]
                order[_k] = newval

        return hold, order

    def do_reduced_simplification(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Perform a number of possible simplification of a Add
        expression after the operands have individually been
        simplified.  Disassociate grouped terms, eliminate zero terms,
        cancel common terms that are subtracted, combine like terms,
        convert repeated addition to multiplication, etc.
        '''
        from proveit.numbers import one, Neg, Mult

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr, assumptions)

        # ungroup the expression (disassociate nested additions).
        _n = 0
        length = len(expr.operands) - 1
        # loop through all operands
        while _n < length:
            operand = expr.operands[_n]
            if (isinstance(operand, ExprRange) and
                    operand.is_parameter_independent):
                # A range of repeated terms may be simplified to
                # a multiplication, but we need to group it first.
                expr = eq.update(expr.association(_n, 1, assumptions))
                expr = eq.update(expr.inner_expr().operands[_n].simplification(
                    assumptions))
            # print("n, length", n, length)
            if (isinstance(operand, Add) or
                    (isinstance(operand, Neg) and
                     isinstance(operand.operand, Add))):
                # if it is grouped, ungroup it
                expr = eq.update(expr.disassociation(_n, assumptions))
            length = len(expr.operands)
            _n += 1

        # eliminate zeros where possible
        expr = eq.update(expr.zero_eliminations(assumptions))
        if not isinstance(expr, Add):
            # eliminated all but one term
            return eq.relation

        # perform cancelations where possible
        expr = eq.update(expr.cancelations(assumptions))
        if not isinstance(expr, Add):
            # canceled all but one term
            return eq.relation

        # Check for any double-negations.
        # Normally, this would have been dealt with in the initial
        # reduction, but can emerge after disassociating a subtraction.
        for _i in range(len(expr.operands)):
            if (isinstance(expr.operands[_i], Neg) and
                    isinstance(expr.operands[_i].operand, Neg)):
                inner_expr = expr.inner_expr().operands[_i]
                expr = eq.update(
                    inner_expr.double_neg_simplification(
                        assumptions=assumptions))

        # separate the types of operands in a dictionary
        hold, order = expr._createDict(assumptions)

        # Have the basic numbers come at the end.
        if order[-1] != one and one in hold:
            order.pop(order.index(one))
            order.append(one)

        if len(order) > 0:
            # Reorder the terms so like terms are adjacent.
            pos = 0
            # The indices keep moving as we reorder, so keep on top of this.
            old2new = {_k: _k for _k in range(len(expr.operands))}
            new2old = {_k: _k for _k in range(len(expr.operands))}
            for key in order:
                for orig_idx in hold[key]:
                    start_idx = old2new[orig_idx]
                    if start_idx == pos:
                        pos += 1
                        continue  # no change. move on.
                    expr = eq.update(
                        expr.commutation(
                            start_idx,
                            pos,
                            assumptions=assumptions))
                    old2new[new2old[start_idx]] = pos
                    orig_old_idx = new2old[start_idx]
                    if start_idx < pos:
                        # decrement indices
                        for new_idx in range(start_idx, pos):
                            new2old[new_idx] = new2old[new_idx + 1]
                            old2new[new2old[new_idx]] -= 1
                    else:
                        # increment indices
                        for new_idx in range(start_idx, pos, -1):
                            new2old[new_idx] = new2old[new_idx - 1]
                            old2new[new2old[new_idx]] += 1
                    new2old[pos] = orig_old_idx
                    pos += 1

            # Now group the terms so we can combine them.
            for _m, key in enumerate(order):
                if len(hold[key]) > 1:
                    expr = eq.update(expr.association(
                        _m, length=len(hold[key]),
                        assumptions=assumptions))

        if len(order) == 1:
            # All operands are like terms.  Simplify by combining them.

            # If all the operands are the same, combine via multiplication.
            if (all(operand == expr.operands[0] for operand in expr.operands)
                    and not (len(expr.operands) == 1 and
                             isinstance(expr.operands[0], ExprRange) and
                             not expr.operands[0].is_parameter_independent)):
                expr = eq.update(
                    expr.conversion_to_multiplication(assumptions))
                expr = eq.update(expr.simplification(assumptions))
                return eq.relation
            elif key != one:
                # for all the keys that are not basic numbers, derive the multiplication from the addition
                # make sure all the operands in the key are products (multiplication)
                # if it's grouped, send it to become a multiplication
                expr = eq.update(
                    expr.factorization(
                        key,
                        pull="right",
                        assumptions=assumptions))
                sub = expr.operands[0].simplification(assumptions)
                eq.update(
                    sub.substitution(
                        expr.inner_expr().operands[0],
                        assumptions))
                return eq.relation

        # simplify the combined terms
        for _i, operand in enumerate(expr.operands):
            if isinstance(operand, Add):
                expr = eq.update(
                    expr.inner_expr().operands[_i].simplification(assumptions))
            elif isinstance(operand, Mult):
                if isinstance(operand.operands[0], Add):
                    expr = eq.update(
                        expr.inner_expr().operands[_i].operands[0].simplification(assumptions))
                if isinstance(
                        expr.operands[_i].operands[0], Add) and len(
                        expr.operands[_i].operands[0].operands) == 1:
                    from proveit.numbers.addition._axioms_ import single_add
                    sub = single_add.instantiate(
                        {x: expr.operands[_i].operands[0].operands[0]})
                    # print("single Add", sub)
                    expr = eq.update(
                        sub.substitution(
                            expr.inner_expr().operands[_i].operands[0],
                            assumptions))

        # ungroup the expression
        _n = 0
        length = len(expr.operands) - 1
        while _n < length:
            # loop through all operands
            # print("n, length", n, length)
            if isinstance(expr.operands[_n], Add):
                # if it is grouped, ungroup it
                # print("to ungroup")
                expr = eq.update(expr.disassociation(_n, assumptions))
            length = len(expr.operands)
            _n += 1
        # print("expr after initial ungroup", expr)
        # print("expr after evaluation", expr)
        # print("last equals!")
        return eq.relation

    def _integerBinaryEval(self, assumptions=USE_DEFAULTS):
        '''
        Evaluate the sum of possibly negated single digit numbers.
        '''
        from proveit.numbers import Neg, is_literal_int, num
        from proveit.numbers.numerals import NumeralSequence
        abs_terms = [
            term.operand if isinstance(
                term, Neg) else term for term in self.terms]
        if len(abs_terms) != 2 or not all(is_literal_int(abs_term)
                                          for abs_term in abs_terms):
            raise ValueError(
                "_integerBinaryEval only applicable for binary addition of integers")
        _a, _b = self.terms
        _a, _b = _a.as_int(), _b.as_int()
        if _a < 0 and _b < 0:
            # evaluate -a-b via a+b
            _a, _b = -_a, -_b
        if _a < 0:
            # evaluate -a+b via (a-b)+b or (b-a)+a
            _a = -_a
            if _a > _b:
                _a, _b = _a - _b, _b
            else:
                _a, _b = _b - _a, _a
        elif _b < 0:
            # evaluate a-b via (a-b)+b or (b-a)+a
            _b = -_b
            if _a > _b:
                _a, _b = _a - _b, _b
            else:
                _a, _b = _b - _a, _a
        assert _a >= 0 and _b >= 0
        #print(_a, _b)
        if not all(term in DIGITS for term in (num(_a), num(_b))):
            if isinstance(num(_a), NumeralSequence):
                return num(_a).num_add_eval(_b, assumptions=assumptions)
            elif isinstance(num(_b), NumeralSequence):
                return num(_a).num_add_eval(_b, assumptions=assumptions)
            raise NotImplementedError(
                "Currently, _integerBinaryEval only works for integer "
                " addition and related subtractions: %d, %d" % (_a, _b))
        if (_a, _b) not in Add.added_numerals:
            try:
                # for single digit addition, import the theorem that provides
                # the evaluation
                Add.added_numerals.add((_a, _b))
                proveit.numbers.numerals.decimals._theorems_.__getattr__(
                    'add_%d_%d' % (_a, _b))
            except BaseException:
                # may fail before the relevent _commons_ and _theorems_ have
                # been generated
                pass  # and that's okay
        # Should have an evaluation now.
        if self not in Equals.known_evaluation_sets:
            raise Exception(
                "Should have an evaluation for %s now.  Why not?  "
                "Perhaps we were not able to prove that the involved numbers "
                "are in the Complex set." %
                self)
        return self.evaluation()

    def do_reduced_evaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        created by JML on 7/31/19. modified by WMW on 9/7/19.
        evaluate literals in a given expression (used for simplification)
        '''
        from proveit.logic import EvaluationError
        from proveit.numbers import Neg, is_literal_int

        abs_terms = [
            term.operand if isinstance(
                term, Neg) else term for term in self.terms]
        if len(abs_terms) == 2 and all(is_literal_int(abs_term)
                                       for abs_term in abs_terms):
            evaluation = self._integerBinaryEval(assumptions=assumptions)
            return evaluation

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr, assumptions)

        # start with cancelations (maybe everything cancels to zero)
        expr = eq.update(expr.cancelations(assumptions))
        if is_irreducible_value(expr):
            return eq.relation

        if not isinstance(expr, Add):
            raise EvaluationError(eq.expr, assumptions)

        # If all the operands are the same, combine via multiplication and then
        # evaluate.
        if all(operand == expr.operands[0] for operand in expr.operands):
            expr = eq.update(expr.conversion_to_multiplication(assumptions))
            eq.update(expr.evaluation(assumptions))
            return eq.relation

        if len(expr.operands) > 2:
            expr = eq.update(pairwise_evaluation(expr, assumptions))
            return eq.relation

        if len(expr.operands) == 2:
            # If both operands are negated, factor out the negation.
            if all(isinstance(operand, Neg) for operand in expr.operands):
                negated = Neg(
                    Add(*[operand.operand for operand in expr.operands]))
                neg_distribution = negated.distribution(assumptions)
                expr = eq.update(neg_distribution.derive_reversed())
                eq.update(expr.evaluation(assumptions))
                return eq.relation

        raise EvaluationError(self, assumptions)

    def subtraction_folding(self, term_idx=None, assumptions=frozenset()):
        '''
        Given a negated term, term_idx or the first negated term if term_idx is None,
        deduce the equivalence between self and a Subtract form (with the specified
        negated term on the right of the subtraction).  Assumptions
        may be necessary to deduce operands being in the set of Complex numbers.
        '''
        from proveit.numbers import Neg
        from proveit.numbers.addition.subtraction.theorems import add_neg_as_subtract
        if term_idx is None:
            for _k, term in enumerate(self.terms):
                if isinstance(term, Neg):
                    term_idx = _k
                    break
            if term_idx is None:
                raise Exception(
                    "No negated term, can't provide the subtraction folding.")
        if not isinstance(self.terms[term_idx], Neg):
            raise ValueError(
                "Specified term is not negated, can't provide the subtraction folding.")
        expr = self
        if term_idx != -1 and term_idx != len(expr.terms) - 1:
            # put the negative term at the end
            expr = expr.commute(term_idx, term_idx + 1, -1)
        if len(expr.terms) > 2:
            # group all of the other terms
            expr = expr.group(0, -1)
        return add_neg_as_subtract.instantiate(
            {x: expr.operands[0], y: expr.operands[-1].operand})

    """
    def deduce_in_natural_pos_directly(self, assumptions=frozenset(), ruled_out_sets=frozenset(), dont_try_pos=False, dont_try_neg=False):
        '''
        If all of the terms are in Natural and just one is positive, then the sum is positive.
        '''
        from proveit.numbers.number_sets import DeduceInNumberSetException, deduce_positive
        from ._theorems_ import add_nat_pos_closure
        from proveit.numbers import NaturalPos, num
        # first make sure all the terms are in Natural
        for _k, term in enumerate(self.operands):
            #try:
                # found one positive term to make the sum positive
            deduce_positive(term, assumptions)
            return add_nat_pos_closure.instantiate({i:num(_k), n:num(len(self.operands)-_k-1), a:self.operands[:_k], b:term, c:self.operands[_k+1:]}, assumptions=assumptions)
            #except:
               # pass
        # need to have one of the elements positive for the sum to be positive
        raise DeduceInNumberSetException(self, NaturalPos, assumptions)
    """

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        given a number set, attempt to prove that the given expression is in that
        number set using the appropriate closure theorem
        '''
        from proveit.numbers.addition._theorems_ import (
            add_int_closure_bin,
            add_int_closure,
            add_nat_closure_bin,
            add_nat_closure,
            add_nat_pos_closure,
            add_nat_pos_from_non_neg,
            add_real_closure_bin,
            add_real_closure,
            add_real_non_neg_closure,
            add_real_non_neg_closure_bin,
            add_real_pos_closure,
            add_real_pos_closure_bin,
            add_real_pos_from_non_neg,
            add_complex_closure,
            add_complex_closure_bin)
        from proveit.numbers.addition.subtraction._theorems_ import (
            subtract_nat_closure_bin, sub_one_is_nat)
        from proveit.numbers import (zero, one, num, Neg, Greater,
                                     Integer, Natural, Real, RealPos,
                                     RealNonNeg, Complex, NaturalPos)
        from proveit.logic import InSet
        if number_set == Integer:
            if len(self.operands) == 2:
                return add_int_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return add_int_closure.instantiate(
                {i: num(len(self.operands)), a: self.operands}, assumptions=assumptions)
        if number_set == Natural:
            if len(self.operands) == 2:
                if isinstance(self.operands[1], Neg):
                    # A subtraction case:
                    if self.operands[1].operand == one:
                        # Special a-1 in Natural case.  If a is
                        # in NaturalPos, we are good.
                        return sub_one_is_nat.instantiate(
                            {a: self.operands[0]}, assumptions=assumptions)
                    # (a-b) in Natural requires that b <= a.
                    return subtract_nat_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1].operand},
                        assumptions=assumptions)
                return add_nat_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]},
                    assumptions=assumptions)
            return add_nat_closure.instantiate(
                {i: num(len(self.operands)), a: self.operands},
                assumptions=assumptions)
        if (number_set == NaturalPos or number_set == RealPos and not
                all(InSet(operand, number_set).proven(assumptions) for
                    operand in self.operands)):
            # Unless we know that all of the operands are in the
            # positive number set, our last resort will be if we know
            # one of the operands is greater than zero.
            val = -1
            for _i, operand in enumerate(self.operands):
                if Greater(operand, zero).proven(assumptions=assumptions):
                    val = _i
                    # print(b)
                    break
            if val == -1:
                raise ProofFailure(InSet(self, number_set), assumptions,
                                   "Expecting at least one value to be "
                                   "known to be greater than zero")
            # print(len(self.operands))
            if number_set == NaturalPos:
                temp_thm = add_nat_pos_from_non_neg
            else:
                temp_thm = add_real_pos_from_non_neg
            #print(temp_thm, {i: num(val), j:num(len(self.operands) - val - 1), a:self.operands[:val], b: self.operands[val], c: self.operands[val + 1:]})
            return temp_thm.instantiate({i: num(val),
                                         j: num(len(self.operands) - val - 1),
                                         a: self.operands[:val],
                                         b: self.operands[val],
                                         c: self.operands[val + 1:]},
                                        assumptions=assumptions)
        if number_set == RealPos:
            if len(self.operands) == 2:
                return add_real_pos_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return add_real_pos_closure.instantiate(
                {i: num(len(self.operands)), a: self.operands}, assumptions=assumptions)
        if number_set == RealNonNeg:
            if len(self.operands) == 2:
                return add_real_non_neg_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return add_real_non_neg_closure.instantiate(
                {i: num(len(self.operands)), a: self.operands}, assumptions=assumptions)
        if number_set == Real:
            if len(self.operands) == 2:
                return add_real_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return add_real_closure.instantiate(
                {i: num(len(self.operands)), a: self.operands}, assumptions=assumptions)
        if number_set == Complex:
            if len(self.operands) == 2:
                return add_complex_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]}, assumptions=assumptions)
            return add_complex_closure.instantiate(
                {i: num(len(self.operands)), a: self.operands}, assumptions=assumptions)
        msg = "'deduce_in_number_set' not implemented for the %s set" % str(
            number_set)
        raise ProofFailure(InSet(self, number_set), assumptions, msg)

    def deduce_difference_in_natural(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Neg
        from proveit.numbers.number_sets.integers._theorems_ import difference_is_nat
        if len(self.terms) != 2:
            raise ValueError("deduce_difference_in_natural only applicable "
                             "when there are two terms, got %s" % self)
        if not isinstance(self.terms[1], Neg):
            raise ValueError("deduce_difference_in_natural only applicable "
                             "for a subtraction, got %s" % self)
        thm = difference_is_nat
        return thm.instantiate({a: self.terms[0], b: self.terms[1].operand},
                               assumptions=assumptions)

    def deduce_difference_in_natural_pos(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Neg
        from proveit.numbers.number_sets.integers._theorems_ import difference_is_nat_pos
        if len(self.terms) != 2:
            raise ValueError(
                "deduce_difference_in_natural_pos only applicable "
                "when there are two terms, got %s" %
                self)
        if not isinstance(self.terms[1], Neg):
            raise ValueError(
                "deduce_difference_in_natural_pos only applicable "
                "for a subtraction, got %s" %
                self)
        thm = difference_is_nat_pos
        return thm.instantiate({a: self.terms[0], b: self.terms[1].operand},
                               assumptions=assumptions)

    def deduce_strict_increase(
            self,
            lower_bound_term_index,
            assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealPos, deduce an return
        the statement that the sum is greater than the term at lower_bound_term_index.
        Assumptions may be needed to deduce that the terms are in RealPos or Real.
        '''
        from ._theorems_ import strictly_increasing_additions
        return strictly_increasing_additions.instantiate(
            {a: self.terms[:lower_bound_term_index],
             c: self.terms[lower_bound_term_index + 1:]},
            assumptions=assumptions).instantiate(
            {b: self.terms[lower_bound_term_index]},
            assumptions=assumptions)

    def deduce_strict_decrease(
            self,
            upper_bound_term_index,
            assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealNeg, deduce an return
        the statement that the sum is less than the term at upper_bound_term_index.
        Assumptions may be needed to deduce that the terms are in RealPos or Real.
        '''
        from ._theorems_ import strictly_decreasing_additions
        return strictly_decreasing_additions.instantiate(
            {a: self.terms[:upper_bound_term_index],
             c: self.terms[upper_bound_term_index + 1:]}).instantiate(
            {b: self.terms[upper_bound_term_index]},
            assumptions=assumptions)

    def factorization(
            self,
            the_factor,
            pull="left",
            group_factor=True,
            assumptions=USE_DEFAULTS):
        '''
        Factor out "the_factor" from this sum, pulling it either to the "left" or "right".
        If group_factor is True and the_factor is a product, these operands are grouped
        together as a sub-product.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in the Complex numbers so that
        the associative and commutation theorems are applicable.
        '''
        from proveit.numbers.multiplication._theorems_ import distribute_through_sum
        from proveit.numbers import num, one, Mult
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr, assumptions)
        _b = []
        # factor the_factor from each term
        for _i in range(len(expr.terms)):
            term = expr.terms[_i]
            if hasattr(term, 'factorization'):
                term_factorization = term.factorization(
                    the_factor,
                    pull,
                    group_factor=group_factor,
                    group_remainder=True,
                    assumptions=assumptions)
                if not isinstance(term_factorization.rhs, Mult):
                    raise Exception(
                        'Expecting right hand size of factorization to be a product')
                if pull == 'left':
                    # the grouped remainder on the right
                    _b.append(term_factorization.rhs.operands[-1])
                else:
                    # the grouped remainder on the left
                    _b.append(term_factorization.rhs.operands[0])
            else:
                if term != the_factor:
                    raise ValueError(
                        "Factor, %s, is not present in the term at index %d of %s!" %
                        (the_factor, _i, self))
                factored_term = Mult(
                    one, term) if pull == 'right' else Mult(
                    term, one)
                term_factorization = factored_term.simplification(
                    assumptions).derive_reversed(assumptions)
                _b.append(one)
            # substitute in the factorized term
            expr = eq.update(term_factorization.substitution(
                expr.inner_expr().terms[_i], assumptions=assumptions))
        if not group_factor and isinstance(the_factor, Mult):
            factor_sub = the_factor.operands
        else:
            factor_sub = [the_factor]
        if pull == 'left':
            _a = factor_sub
            _c = []
        else:
            _a = []
            _c = factor_sub
        _i = num(len(_a))
        _j = num(len(_b))
        _k = num(len(_c))
        eq.update(distribute_through_sum.instantiate(
            {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c},
            assumptions=assumptions).derive_reversed(assumptions))
        return eq.relation

    def commutation(
            self,
            init_idx=None,
            final_idx=None,
            assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, (a + b + ... + y + z) = (a + ... + y + b + z)
        via init_idx = 1 and final_idx = -2.
        '''
        from ._theorems_ import commutation, leftward_commutation, rightward_commutation
        eq = apply_commutation_thm(
            self,
            init_idx,
            final_idx,
            commutation,
            leftward_commutation,
            rightward_commutation,
            assumptions)
        '''
        # DON'T WORRY ABOUT RESETTING THE STYLE FOR THE MOMENT.

        # set the subraction style as appropriate:
        subtraction_positions = self.subtraction_positions()
        eq.inner_expr().lhs.with_subtraction_at(*subtraction_positions)

        eq.inner_expr().rhs.with_subtraction_at(*)
        '''
        return eq

    def group_commutation(
            self,
            init_idx,
            final_idx,
            length,
            disassociate=True,
            assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operands
        at indices [init_idx, init_idx+length) have been moved to [final_idx. final_idx+length).
        It will do this by performing association first.  If disassocate is True, it
        will be disassociated afterwards.
        '''
        return group_commutation(
            self,
            init_idx,
            final_idx,
            length,
            disassociate,
            assumptions)

    def association(self, start_idx, length, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (a + b + ... + y + z) = (a + b ... + (l + ... + m) + ... + y + z)
        '''
        from ._theorems_ import association
        eq = apply_association_thm(
            self, start_idx, length, association, assumptions)

        '''
        # DON'T WORRY ABOUT RESETTING THE STYLE FOR THE MOMENT.
        # set the subraction style as appropriate given what we started with:
        subtraction_positions = self.subtraction_positions()
        eq.inner_expr().lhs.with_subtraction_at(*subtraction_positions)
        beg_positions = [p for p in subtraction_positions if p < start_idx]
        inner_positions = [p-start_idx for p in subtraction_positions if start_idx <= p < start_idx+length]
        end_positions = [p-length for p in subtraction_positions if p > start_idx+length]
        eq.inner_expr().rhs.operands[start_idx].with_subtraction_at(*inner_positions)
        eq.inner_expr().rhs.operands[start_idx].with_subtraction_at(*(beg_positions + end_positions))
        '''
        return eq

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a + b ... + (l + ... + m) + ... + y+ z) = (a + b + ... + y + z)
        '''
        from proveit.core_expr_types import Len
        from proveit.numbers import Neg
        from ._theorems_ import disassociation
        from .subtraction._theorems_ import subtraction_disassociation

        if (isinstance(self.operands[idx], Neg) and
                isinstance(self.operands[idx].operand, Add)):
            subtraction_terms = self.operands[idx].operand.operands
            _a = self.operands[:idx]
            _b = subtraction_terms
            _c = self.operands[idx + 1:]
            _i = Len(_a).computed(assumptions)
            _j = Len(_b).computed(assumptions)
            _k = Len(_c).computed(assumptions)
            return subtraction_disassociation.instantiate(
                {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c},
                assumptions=assumptions)
        eq = apply_disassociation_thm(self, idx, disassociation, assumptions)
        '''
        # DON'T WORRY ABOUT RESETTING THE STYLE FOR THE MOMENT.
        # set the subraction style as appropriate given what we started with:
        subtraction_positions = self.subtraction_positions()
        inner_positions = self.operand[idx].subtraction_positions()
        inner_num_operands = len(self.operand[idx])
        eq.inner_expr().lhs.operands[idx].with_subtraction_at(*inner_positions)
        eq.inner_expr().lhs.with_subtraction_at(*subtraction_positions)
        new_positions = [p for p in subtraction_positions if p < idx]
        new_positions.extend([p+idx for p in inner_positions])
        new_positions.extend([p+inner_num_operands for p in subtraction_positions if p > idx])
        eq.inner_expr().rhs.with_subtraction_at(*new_positions)
        '''
        return eq


def subtract(a, b):
    '''
    Return the a-b expression (which is internally a+(-b)).
    '''
    from proveit.numbers import Neg
    if isinstance(b, ExprRange):
        b = ExprRange(b.lambda_map.parameter_or_parameters,
                      Neg(b.lambda_map.body), b.start_index,
                      b.end_index, b.get_styles())
        # The default style will use subtractions where appropriate.
        return Add(a, b)
    return Add(a, Neg(b))


def dist_subtract(a, b):
    '''
    Returns the distributed a-b expression.  That is, if a or b are
    Add expressions, combine all of the terms into a single Add
    expression (not nested).  For example, with
    a:x-y, b:c+d-e+g, it would return x-y-c-d+e-g.
    '''
    from proveit.numbers import Neg
    if isinstance(b, Add):
        bterms = [term.operand if isinstance(term, Neg) else Neg(term)
                  for term in b.terms]
    elif isinstance(b, ExprRange):
        bterms = [ExprRange(b.lambda_map.parameter_or_parameters,
                            Neg(b.lambda_map.body), b.start_index,
                            b.end_index, b.get_styles())]
    else:
        bterms = [Neg(b)]
    if isinstance(a, Add):
        aterms = a.terms
    else:
        aterms = [a]
    # The default style will use subtractions where appropriate.
    return Add(*(aterms + bterms))


def dist_add(*terms):
    '''
    Returns the distributed sum of expression.  That is, if any of
    the terms are Add expressions, expand them.  For example,
    dist_add(x-y, c+d-e+g) would return x-y+c+d-e+g.
    '''
    expanded_terms = []
    for term in terms:
        if isinstance(term, Add):
            expanded_terms.extend(term.terms)
        else:
            expanded_terms.append(term)
    return Add(*expanded_terms)


def const_shift_decomposition(idx):
    '''
    Return a tuple whose sum is the given 'idx' where the
    first element is an Expression and the second element is an
    integer.  There are three cases:
        1) given an integer i as an Expression, return (zero, i).
        2) given x+i where i is an integer as an Expression,
            return (x, i).
        3) given x, return (x, 0).
    '''
    from proveit.numbers import zero, is_literal_int
    if is_literal_int(idx):
        return (zero, idx.as_int())
    elif (isinstance(idx, Add) and len(idx.operands) == 2
          and is_literal_int(idx.operands[1])):
        return (idx.operands[0], idx.operands[1].as_int())
    return (idx, 0)


def const_shift_composition(idx, shift):
    '''
    Return an expression representing the 'idx' shifted by amount
    'shift' where 'shift' is a Python integer.  This will be
    Add(idx, num(shift)) except for the special cases when
    shift==0 or idx==zero and it reduces.
    '''
    from proveit.numbers import num, zero
    assert isinstance(shift, int)
    if shift == 0:
        return idx
    if idx == zero:
        return num(shift)
    return Add(idx, num(shift))


# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(
    Add, 'commutation', 'commuted', 'commute')
InnerExpr.register_equivalence_method(
    Add,
    'group_commutation',
    'group_commuted',
    'group_commute')
InnerExpr.register_equivalence_method(
    Add, 'association', 'associated', 'associate')
InnerExpr.register_equivalence_method(
    Add, 'disassociation', 'disassociated', 'disassociate')
InnerExpr.register_equivalence_method(
    Add, 'factorization', 'factorized', 'factor')
InnerExpr.register_equivalence_method(Add, 'cancelation', 'canceled', 'cancel')
InnerExpr.register_equivalence_method(
    Add, 'cancelations', 'all_canceled', 'all_cancel')
InnerExpr.register_equivalence_method(
    Add,
    'zero_elimination',
    'eliminated_zero',
    'eliminate_zero')
InnerExpr.register_equivalence_method(
    Add,
    'zero_eliminations',
    'eliminated_zeros',
    'eliminate_zeros')
