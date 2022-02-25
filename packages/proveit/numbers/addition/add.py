import bisect
from collections import deque

from proveit import (Expression, Judgment, Literal, Operation, ExprTuple,
                     ExprRange, defaults, USE_DEFAULTS, StyleOptions, 
                     prover, relation_prover, equality_prover,
                     maybe_fenced_latex, ProofFailure, InnerExpr,
                     UnsatisfiedPrerequisites,
                     SimplificationDirectives, TransRelUpdater)
from proveit import a, b, c, d, i, j, k, l, n, x, y, free_vars
from proveit.logic import (And, Equals, NotEquals,
                           EvaluationError, InSet)
from proveit.logic.irreducible_value import is_irreducible_value
from proveit.numbers import NumberOperation
from proveit.numbers.numerals.decimals import DIGITS
import proveit.numbers.numerals.decimals
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, group_commutation, pairwise_evaluation
from proveit import TransRelUpdater
import bisect
from proveit.numbers import (NumberOperation, sorted_number_sets,
                             deduce_number_set)
from proveit.numbers import (Integer, IntegerNeg, IntegerNonPos,
                             Natural, NaturalPos, IntegerNonZero,
                             Rational, RationalPos, RationalNonZero,
                             RationalNeg, RationalNonNeg,
                             RationalNonPos,
                             Real, RealPos, RealNeg, RealNonNeg,
                             RealNonPos, RealNonZero, Complex, 
                             ComplexNonZero)


class Add(NumberOperation):
    # operator of the Add operation
    _operator_ = Literal(string_format='+', theory=__file__)
    
    # The 'order_key' simplification directive can be used
    # to sort terms in a particular order.  By default, there
    # is no sorting -- it keeps the original order as much as
    # possible but still combines like terms.
    _simplification_directives_ = SimplificationDirectives(
            ungroup = True,
            order_key = lambda term : 0)

    # Map terms to sets of Judgment equalities that involve
    # the term on the left hand side.
    known_equalities = dict()

    def __init__(self, *operands, styles=None):
        r'''
        Add together any number of operands.
        '''
        NumberOperation.__init__(self, Add._operator_, operands, 
                                 styles=styles)
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

    def _formatted(self, format_type, **kwargs):
        '''
        Override Operation._formatted so to enable subtraction notation where desired.
        '''
        from proveit import ExprRange
        from proveit.numbers import Neg
        
        # Where should we use subtraction notation 
        subtraction_positions = []        
        for _k, operand in enumerate(self.operands.entries):
            if isinstance(operand, Neg):
                if operand.use_subtraction_notation():
                    subtraction_positions.append(_k)
            elif isinstance(operand, ExprRange):
                if isinstance(operand.body, Neg):
                    if operand.body.use_subtraction_notation():
                        subtraction_positions.append(_k)
        
        if len(subtraction_positions) > 0:
            operators = []
            operands = list(self.operands.entries)
            for operand in operands:
                if isinstance(operand, ExprRange):
                    # Make the operator an ExprRange in correspondence
                    # with the operands ExprRange
                    operators.append(
                        ExprRange(
                            operand.lambda_map.parameter_or_parameters,
                            self.operator,
                            operand.true_start_index,
                            operand.true_end_index))
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
                            operand.true_start_index,
                            operand.true_end_index)
                        operands[pos] = ExprRange(
                            operand.lambda_map.parameter,
                            operand.lambda_map.body.operand,
                            operand.true_start_index,
                            operand.true_end_index) .with_styles(
                            **operand.get_styles())
                elif pos == 0:
                    # not negated after all -- revert to the "implicit first
                    # operator" default
                    implicit_first_operator = False
            return Operation._formatted_operation(
                format_type,
                operators,
                operands,
                implicit_first_operator=implicit_first_operator,
                wrap_positions=self.wrap_positions(),
                justification=self.get_style('justification', 'left'),
                **kwargs)
        else:
            return Operation._formatted_operation(
                format_type,
                self.operator,
                self.operands,
                wrap_positions=self.wrap_positions(),
                justification=self.get_style('justification', 'left'),
                **kwargs)

    def remake_constructor(self):
        from proveit.numbers import Neg
        if (self.operands.is_double() 
                and isinstance(self.operands[1], Neg)
                and self.operands[1].use_subtraction_notation()):
            return 'subtract'  # use a different constructor if using the subtraction style
        return Operation.remake_constructor(self)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        from proveit.numbers import Neg
        if (self.operands.is_double() 
                and isinstance(self.operands[1], Neg)
                and self.operands[1].use_subtraction_notation()):
            yield self.operands[0]
            assert isinstance(
                self.operands[1], Neg), "The second operand must be negated"
            yield self.operands[1].operand
        else:
            for operand in self.operands:
                yield operand

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
                Add.known_equalities.setdefault(term, set()).add(judgment)

            if addition.terms.is_double():
                # deduce the commutation form: b+a=c from a+b=c
                if addition.terms[0] != addition.terms[1]:
                    yield (lambda : judgment.inner_expr().lhs.commute(0, 1))

                if all(not isinstance(term, Neg) for term in addition.terms):
                    # From a+b=c
                    # deduce the negations form: -a-b=-c
                    #      the subtraction form: c-b=a
                    #      and the reversed subtraction form: b-c = -a
                    yield (lambda : self.equation_negation(judgment.rhs))
                    yield (lambda : self.equation_subtraction(judgment.rhs))
                    yield (lambda : self.equation_reversed_subtraction(
                            judgment.rhs))

    @prover
    def equation_negation(self, rhs, **defaults_config):
        '''
        From (a + b) = rhs, derive and return -(a-b) = -rhs
        '''
        from proveit.numbers.addition.subtraction import negated_add
        if not self.terms.is_double():
            raise NotImplementedError(
                "Add.equation_negation implemented only when there are two "
                "and only two added terms")
        _a, _b = self.terms[0], self.terms[1]
        deduction = negated_add.instantiate(
            {a: _a, b: _b, c: rhs}, auto_simplify=False)
        return deduction

    @prover
    def equation_subtraction(self, rhs, **defaults_config):
        '''
        From (a + b) = rhs, derive and return rhs - b = a.
        '''
        from proveit.numbers.addition.subtraction import subtract_from_add
        if not self.terms.is_double():
            raise NotImplementedError(
                "Add.deduce_subtraction implemented only when there are "
                "two and only two added terms")
        _a, _b = self.terms[0], self.terms[1]
        deduction = subtract_from_add.instantiate(
            {a: _a, b: _b, c: rhs}, auto_simplify=False)
        return deduction

    @prover
    def equation_reversed_subtraction(self, rhs, **defaults_config):
        '''
        From (a + b) = rhs, derive and return b - rhs = -a.
        '''
        from proveit.numbers.addition.subtraction import subtract_from_add_reversed
        if not self.terms.is_double():
            raise NotImplementedError(
                "Add.decude_reversed_subtraction implemented only when "
                "there are two and only two added terms")
        deduction = subtract_from_add_reversed.instantiate(
            {a: self.terms[0], b: self.terms[1], c: rhs},
            auto_simplify=False)
        return deduction

    @equality_prover('multiplied', 'multiply')
    def conversion_to_multiplication(self, **defaults_config):
        '''
        From the addition of the same values, derive and return
        the equivalence as a multiplication. For example,
        a + a + a = 3 * a
        '''
        from proveit import ExprRange
        from proveit.numbers import one
        from proveit.numbers.multiplication import (
            mult_def_rev, repeated_addition_to_mult)
        if not all(operand == self.operands[0] for operand in self.operands):
            raise ValueError(
                "'as_mult' is only applicable on an 'Add' expression "
                "if all operands are the same: %s" %
                str(self))
        if (self.operands.num_entries() == 1 
                and isinstance(self.operands[0], ExprRange)
                and self.operands[0].is_parameter_independent
                and self.operands[0].true_start_index == one):
            expr_range = self.operands[0]
            return repeated_addition_to_mult.instantiate(
                {x: expr_range.body, n: expr_range.true_end_index})
        _n = self.operands.num_elements()
        _a = self.operands
        _x = self.operands[1]
        return mult_def_rev.instantiate({n: _n, a: _a, x: _x})

    @equality_prover('all_canceled', 'all_cancel')
    def cancelations(self, **defaults_config):
        '''
        Deduce and return an equality between self and a form in which
        all simple cancellations are performed (where there are exact
        negations that occur).
        '''
        from proveit.numbers import Neg
        expr = self

        # A convenience to allow successive update to the equation via 
        # transitivities. (starting with self=self).
        eq = TransRelUpdater(self)

        neg_operand_indices = dict()
        for _i, operand in enumerate(self.operands.entries):
            if isinstance(operand, Neg):
                neg_operand_indices.setdefault(operand.operand, set()).add(_i)

        canceled_indices = []
        for _i, operand in enumerate(self.operands.entries):
            if isinstance(operand, Neg):
                continue
            if operand in neg_operand_indices:
                indices = neg_operand_indices[operand]
                _j = indices.pop()
                if len(indices) == 0:
                    # no more indices to use in the future
                    neg_operand_indices.pop(operand)
                # By finding where i and j will be inserted into the 
                # canceled_indices array, we can figure out how much 
                # they need to shift by to compensate for previous 
                # cancelations.
                i_shift = bisect.bisect_left(canceled_indices, _i)
                j_shift = bisect.bisect_left(canceled_indices, _j)
                # Insert the last one first so we don't need to 
                # compensate:
                if _i < _j:
                    canceled_indices.insert(j_shift, _j)
                    canceled_indices.insert(i_shift, _i)
                else:
                    canceled_indices.insert(i_shift, _i)
                    canceled_indices.insert(j_shift, _j)
                expr = eq.update(expr.cancelation(
                        _i - i_shift, _j - j_shift, preserve_all=True))
        return eq.relation

    @equality_prover('canceled', 'cancel')
    def cancelation(self, idx1, idx2, **defaults_config):
        '''
        Attempt a simple cancelation between operands at index i and j.
        If one of these operands is the negation of the other, deduce
        and return an equality between self and a form in which these
        operands are canceled.
        '''
        from .subtraction import add_cancel_basic, add_cancel_reverse, add_cancel_general, add_cancel_general_rev
        from .subtraction import add_cancel_triple_12, add_cancel_triple_13, add_cancel_triple_23
        from .subtraction import add_cancel_triple_21, add_cancel_triple_31, add_cancel_triple_32
        from proveit.numbers import Neg
        if idx1 > idx2:
            # choose i to be less than j
            return self.cancelation(idx2, idx1)

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

        if self.operands.is_double():
            return basic_thm.instantiate({a: canceled_op})
        elif (not self.operands.contains_range() 
                and self.operands.num_entries() == 3):
            # _k is the 3rd index, completing i and j in the set {0,1,2}.
            _k = {0, 1, 2}.difference([idx1, idx2]).pop()
            thm = triple_thms[2 - _k]
            return thm.instantiate({a: canceled_op, b: self.operands[_k]})
        else:
            _a = self.operands[:idx1]
            _b = canceled_op
            _c = self.operands[idx1 + 1:idx2]
            _d = self.operands[idx2 + 1:]
            _i = _a.num_elements()
            _j = _c.num_elements()
            _k = _d.num_elements()
            return general_thm.instantiate(
                {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c, d: _d})

    @equality_prover('eliminated_zeros', 'eliminate_zeros')   
    def zero_eliminations(self, **defaults_config):
        '''
        Derive and return this Add expression equal to a form in which
        all zero's are eliminated.
        '''
        from proveit.numbers import zero

        expr = self

        # A convenience to allow successive update to the equation via
        # transitivities (starting with self=self).
        eq = TransRelUpdater(self)

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands.entries)):
            if operand == zero:
                idx = self.operands.num_entries() - rev_idx - 1
                expr = eq.update(expr.zero_elimination(
                        idx, preserve_all=True))
                if not isinstance(expr, Add):
                    # can't do an elimination if reduced to a single term.
                    break

        return eq.relation

    @equality_prover('eliminated_zero', 'eliminate_zero')
    def zero_elimination(self, idx, **defaults_config):
        '''
        Derive and return this Add expression equal to a form in which
        a specific zero operand (at the given index) is eliminated.
        '''
        from proveit.numbers import zero
        from . import elim_zero_left, elim_zero_right, elim_zero_any

        if self.operands[idx] != zero:
            raise ValueError(
                "Operand at the index %d expected to be zero for %s" %
                (idx, str(self)))

        if self.operands.is_double():
            if idx == 0:
                return elim_zero_left.instantiate({a: self.operands[1]})
            else:
                return elim_zero_right.instantiate({a: self.operands[0]})
        _a = self.operands[:idx]
        _b = self.operands[idx + 1:]
        _i = _a.num_elements()
        _j = _b.num_elements()
        return elim_zero_any.instantiate({i: _i, j: _j, a: _a, b: _b})

    """
    def derive_expanded_neg_self(self, idx=0, assumptions=USE_DEFAULTS):
        '''
        created by JML on 7/26/19
        given an expression with a term that is a negation of itself cancel them out
        a + b + (-b) + c = a + c
        '''
        from . import expanded_add_neg_self
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

    def _create_dict(self):
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

        for _i, val in enumerate(self.operands.entries):
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
                    if newval.operands.num_entries() > 2:
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

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Add
        expression assuming the operands have been simplified.
        
        Perform a number of possible simplifications of an Add
        expression after the operands have been simplified.  
        Disassociate grouped terms, eliminate zero terms,
        cancel common terms that are subtracted, combine like terms,
        convert repeated addition to multiplication, etc.
        '''
        from proveit.numbers import one, Neg, is_literal_int
        from . import empty_addition, unary_add_reduction
        
        if self.operands.num_entries() == 0:
            # +() = 0
            return empty_addition
        
        if self.operands.is_single():
            return unary_add_reduction.instantiate({a:self.operands[0]},
                                                    preserve_all=True)

        # If all operands are irreducible, perform the evaluation.
        if all(is_irreducible_value(term) for term in self.terms):
            if self.operands.is_double():                
                abs_terms = [
                    term.operand if isinstance(term, Neg) 
                    else term for term in self.terms]
                if all(is_literal_int(abs_term) for abs_term in abs_terms):
                    # Evaluate the addition of two literal integers.
                    evaluation = self._integerBinaryEval()
                    return evaluation
            else:
                # Do a pairwise addition of irreducible terms.         
                return pairwise_evaluation(self)

        # If all operands are negated, factor out the negation.
        if all(isinstance(operand, Neg) for operand in self.operands):
            negated = Neg(
                Add(*[operand.operand for operand in self.operands]))
            neg_distribution = negated.distribution(auto_simplify=True)
            return neg_distribution.derive_reversed()
        
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)
        
        if Add._simplification_directives_.ungroup:
            # ungroup the expression (disassociate nested additions).
            _n = 0
            length = expr.operands.num_entries() - 1
            # loop through all operands
            while _n < length:
                operand = expr.operands[_n]
                if (isinstance(operand, ExprRange) and
                        operand.is_parameter_independent):
                    # A range of repeated terms may be simplified to
                    # a multiplication, but we need to group it first.
                    inner_simplification = (
                            Add(operand).shallow_simplification())
                    expr = eq.update(expr.association(
                            _n, 1, replacements=[inner_simplification],
                            auto_simplify=False))
                # print("n, length", n, length)
                if (isinstance(operand, Add) or
                        (isinstance(operand, Neg) and
                         isinstance(operand.operand, Add))):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, preserve_all=True))
                length = expr.operands.num_entries()
                _n += 1

        # eliminate zeros where possible
        expr = eq.update(expr.zero_eliminations(preserve_all=True))
        if not isinstance(expr, Add):
            # eliminated all but one term
            return eq.relation

        # perform cancelations where possible
        expr = eq.update(expr.cancelations(preserve_all=True))
        if not isinstance(expr, Add):
            # canceled all but one term
            return eq.relation

        # Check for any double-negations.
        # Normally, this would have been dealt with in the initial
        # reduction, but can emerge after disassociating a subtraction.
        for _i in range(expr.operands.num_entries()):
            if (isinstance(expr.operands[_i], Neg) and
                    isinstance(expr.operands[_i].operand, Neg)):
                inner_expr = expr.inner_expr().operands[_i]
                expr = eq.update(
                    inner_expr.double_neg_simplification(
                            preserve_all=True))

        # separate the types of operands in a dictionary
        hold, order = expr._create_dict()
        order_key = Add._simplification_directives_.order_key

        # Have the basic numbers come at the end.
        #if order[-1] != one and one in hold:
        #    order.pop(order.index(one))
        #    order.append(one)
        
        if len(order) > 1:
            # Reorder the terms so like terms are adjacent.
            pos = 0
            # The indices keep moving as we reorder, so keep on top of this.
            old2new = {_k: _k for _k in range(expr.operands.num_entries())}
            new2old = {_k: _k for _k in range(expr.operands.num_entries())}
            for key in sorted(order, key=order_key):
                for orig_idx in hold[key]:
                    start_idx = old2new[orig_idx]
                    if start_idx == pos:
                        pos += 1
                        continue  # no change. move on.
                    expr = eq.update(
                        expr.commutation(start_idx, pos, 
                                         preserve_all=True))
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
                    grouped_term = Add(
                            *expr.operands.entries[_m:_m+len(hold[key])])
                    inner_simplification = (
                            grouped_term.shallow_simplification())
                    expr = eq.update(expr.association(
                        _m, length=len(hold[key]),
                        replacements=[inner_simplification],
                        auto_simplify=False))

        elif len(order) == 1:
            # All operands are like terms.  Simplify by combining them.
            key = order[0]
            # If all the operands are the same, combine via multiplication.
            if (all(operand == expr.operands[0] for operand in expr.operands)
                    and not (expr.operands.num_entries() == 1 and
                             isinstance(expr.operands[0], ExprRange) and
                             not expr.operands[0].is_parameter_independent)):
                expr = eq.update(
                    expr.conversion_to_multiplication(auto_simplify=True))
                return eq.relation
            elif key != one and expr.operands.num_entries() > 1:
                # for all the keys that are not basic numbers, 
                # derive the multiplication from the addition
                # make sure all the operands in the key are products 
                # (multiplication) if it's grouped, send it to become a 
                # multiplication
                expr = eq.update(
                    expr.factorization(key, pull="right", auto_simplify=True))
                return eq.relation
        
        if expr != self:
            # Try starting over with a call to shallow_simplification
            # (an evaluation may already be known).
            eq.update(expr.shallow_simplification(
                    must_evaluate=must_evaluate))
            return eq.relation

        if all(is_irreducible_value(term) for term in self.terms):
            raise NotImplementedError(
                "Addition evaluation only implemented for integers: %s"
                %self)
        
        if must_evaluate:
            # The simplification of the operands may not have
            # worked hard enough.  Let's work harder if we
            # must evaluate.
            for term in self.terms:
                if not is_irreducible_value(term):
                    term.evaluation()
            # Start over now that the terms are all evaluated to
            # irreductible values.
            return self.evaluation()
        return eq.relation
    
    def quick_simplified(self):
        '''
        Return a simplified version of this Add expression
        without any proof.  In particular, negations are distributed
        nested additionas are ungrouped, integers are extracted,
        added, and placed at the end, and cancelations are made on
        individual terms as well as expression ranges or portions of
        expression ranges.  We freely assume terms represent numbers
        and expression ranges are well-formed.
        This quick-n-dirty approach can be good
        enough for the purposes of displaying expressions involving
        expression ranges.  See also the quick_simplified_index 
        function defined in number_operation.py.
        '''
        from proveit.numbers import is_literal_int, num, Neg
        
        # Extract any literal integers and expand nested sums.  
        # While we are at it, determing the extremal shifts at the 
        # heads and tails of expression ranges.
        terms = [] # split into sign, abs_term pairs
        int_sum = 0
        remaining_terms = deque(self.terms)
        sign=1
        # Map non-shifted head to latest shift of ExprRange terms:
        latest_head_shift = dict() # (Lambda, index expr) -> int
        # Map non-shiftted tail to earliest shift of ExprRange terms:
        earliest_tail_shift = dict() # (Lambda, index expr) -> int
        all_abs_terms = set()
        while len(remaining_terms):
            term = remaining_terms.popleft()
            if term == Neg:
                # Just an indication to switch the sign back.
                sign = -sign
                continue
            if is_literal_int(term):
                int_sum += sign*term.as_int()
                continue
            if isinstance(term, Neg):
                # Switch the sign and indicate to switch the sign
                # back later.
                sign = -sign
                remaining_terms.appendleft(Neg)
                remaining_terms.appendleft(term.operand)
                continue
            if isinstance(term, Add):
                remaining_terms.extendleft(reversed(term.terms.entries))
                continue
            if isinstance(term, ExprRange):
                start_base, start_shift = split_int_shift(term.true_start_index)
                end_base, end_shift = split_int_shift(term.true_end_index)
                lambda_map = term.lambda_map
                latest_head_shift[(lambda_map, start_base)] = max(
                        start_shift, latest_head_shift.get(
                                (lambda_map, start_base), start_shift))
                earliest_tail_shift[(lambda_map, end_base)] = min(
                        end_shift, earliest_tail_shift.get(
                                (lambda_map, end_base), end_shift))
            all_abs_terms.add(term)
            terms.append((sign, term))
        term = None
                
        # Extend the "latest heads" and "earliest tails" if there
        # are individual terms that match them so we can maximize
        # cancelations.
        for extremal_shifts, step in ((latest_head_shift, 1),
                                      (earliest_tail_shift, -1)):
            for (lambda_map, base), shift in extremal_shifts.items():
                while True:
                    index = Add(base, num(shift)).quick_simplified()
                    _expr = lambda_map.apply(index)
                    if _expr in all_abs_terms:
                        shift += step
                        if (lambda_map.parameter not in
                                free_vars(lambda_map.body)):
                            # avoid an infinite loop
                            break
                    else:
                        break
                extremal_shifts[(lambda_map, base)] = shift
        
        # Expand ExprRange heads and tails to their extremal shifts
        if len(latest_head_shift) > 0:
            old_terms = terms
            terms = []
            for sign, abs_term in old_terms:
                if isinstance(abs_term, ExprRange):
                    start_base, start_shift = split_int_shift(abs_term.true_start_index)
                    end_base, end_shift = split_int_shift(abs_term.true_end_index)
                    lambda_map = abs_term.lambda_map
                    latest_start = latest_head_shift[(lambda_map, start_base)]
                    earliest_end = earliest_tail_shift[(lambda_map, end_base)]
                    if start_base == end_base:
                        # For finite ranges, expand all elements.
                        latest_start = end_shift+1
                    # Peel off elements before the latest start.
                    shift = start_shift
                    while shift < latest_start:
                        index = Add(start_base, num(shift)).quick_simplified()
                        terms.append((sign, lambda_map.apply(index)))
                        shift += 1
                    if start_base == end_base and shift > end_shift:
                        continue # already expanded all elements.
                    start_index = Add(start_base,
                                      num(latest_start)).quick_simplified()
                    end_index = Add(end_base, 
                                    num(earliest_end)).quick_simplified()
                    terms.append((sign, ExprRange(abs_term.parameter, 
                                                  abs_term.body,
                                                  start_index, end_index)))
                    shift = earliest_end + 1
                    # Peel off elements after the earliest end.
                    while shift <= end_shift:
                        index = Add(end_base, num(shift)).quick_simplified()
                        terms.append((sign, lambda_map.apply(index)))
                        shift += 1
                else:
                    terms.append((sign, abs_term))
        
        # Do cancelations of opposite terms.
        # Also check for clearly empty ExprRanges.
        abs_term_to_neg_idx = dict()
        abs_term_to_pos_idx = dict()
        cancelation_indices = set()
        for idx, (sign, abs_term) in enumerate(terms):
            if sign == -1:
                if abs_term in abs_term_to_pos_idx:
                    # Neg term cancels with previous positive term.
                    other_idx = abs_term_to_pos_idx.pop(abs_term)
                    cancelation_indices.add(idx)
                    cancelation_indices.add(other_idx)
                else:
                    # Store for possible cancelation ahead.
                    abs_term_to_neg_idx[abs_term] = idx
            else:
                if abs_term in abs_term_to_neg_idx:
                    # Positive term cancels with previous Neg term.
                    other_idx = abs_term_to_neg_idx.pop(abs_term)
                    cancelation_indices.add(idx)
                    cancelation_indices.add(other_idx)
                else:
                    # Store for possible cancelation ahead.
                    abs_term_to_pos_idx[abs_term] = idx
        terms = [term for idx, term in enumerate(terms) if 
                 idx not in cancelation_indices]
        
        # Re-extend heads and tails of ExprRanges that may have been
        # split apart, now that we've had a chance to find cancelations.
        if len(latest_head_shift) > 0 and len(terms) > 0:
            # Try to prepend heads going in reverse
            old_terms = terms
            reversed_terms = []
            following_term = None
            for sign, abs_term in reversed(old_terms):
                if following_term is not None:
                    if (sign==following_term[0] 
                            and isinstance(following_term[1], ExprRange)):
                        # See if the current term prepends the head of
                        # the following range.
                        start_base, start_shift = split_int_shift(
                                following_term[1].true_start_index)
                        lambda_map = following_term[1].lambda_map
                        index = Add(start_base, 
                                    num(start_shift-1)).quick_simplified()
                        if abs_term == lambda_map.apply(index):
                            # Prepend the head.
                            following_term[1] = ExprRange(
                                    following_term[1].parameter, 
                                    following_term[1].body,
                                    index, following_term[1].true_end_index)
                            continue
                    reversed_terms.append(following_term)
                following_term = [sign, abs_term]
            reversed_terms.append(following_term) # get the last one
            
            # Try to extend tails, reversing again.
            terms = []
            prev_term = None
            for sign, abs_term in reversed(reversed_terms):
                if prev_term is not None:
                    if (sign==prev_term[0] and 
                            isinstance(prev_term[1], ExprRange)):
                        # See if the current term extends the tail of
                        # the previous range.
                        end_base, end_shift = split_int_shift(
                                prev_term[1].true_end_index)
                        lambda_map = prev_term[1].lambda_map
                        index = Add(end_base, 
                                    num(end_shift+1)).quick_simplified()
                        if abs_term == lambda_map.apply(index):
                            # Extend the tail.
                            prev_term[1] = ExprRange(
                                    prev_term[1].parameter, prev_term[1].body,
                                    prev_term[1].true_start_index, index)
                            continue
                    terms.append(prev_term)
                prev_term = [sign, abs_term]
            terms.append(prev_term) # get the last one
        
        # Merge the sign and abs_term into each term.
        for idx, (sign, abs_term) in enumerate(terms):
            if sign==1:
                terms[idx] = abs_term
            else:
                assert sign==-1
                if isinstance(abs_term, ExprRange):
                    terms[idx] = Neg(Add(abs_term))
                else:
                    terms[idx] = Neg(abs_term)
        
        if int_sum == 0:
            if len(terms) == 0:
                return num(0)
            if len(terms) == 1 and not isinstance(terms[0], ExprRange):
                return terms[0]
            return Add(*terms)
        else:
            if len(terms) == 0:
                return num(int_sum)
            return Add(*(terms + [num(int_sum)]))

    def quick_simplification(self):
        '''
        Return a simplification of this Add expression without any 
        proof.  See Add.quick_simplified for more details.
        '''
        return Equals(self, self.quick_simplified())        

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
        with defaults.temporary() as temp_defaults:
            # We rely upon side-effect automation here.
            temp_defaults.automation = True
            # for single digit addition, import the theorem that provides
            # the evaluation
            proveit.numbers.numerals.decimals.__getattr__(
                    'add_%d_%d' % (_a, _b))
        return self.evaluation()

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
            for _k, term in enumerate(self.terms.entries):
                if isinstance(term, Neg):
                    term_idx = _k
                    break
            if term_idx is None:
                raise ValueError(
                    "No negated term, can't provide the subtraction folding.")
        if not isinstance(self.terms[term_idx], Neg):
            raise ValueError(
                "Specified term is not negated, can't provide the subtraction folding.")
        expr = self
        if term_idx != -1 and term_idx != expr.terms.num_entries() - 1:
            # put the negative term at the end
            expr = expr.commute(term_idx, term_idx + 1, -1)
        if expr.terms.num_entries() > 2:
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
        from . import add_nat_pos_closure
        from proveit.numbers import NaturalPos, num
        # first make sure all the terms are in Natural
        for _k, term in enumerate(self.operands):
            #try:
                # found one positive term to make the sum positive
            deduce_positive(term, assumptions)
            return add_nat_pos_closure.instantiate({i:num(_k), n:num(self.operands.num_entries()-_k-1), a:self.operands[:_k], b:term, c:self.operands[_k+1:]}, assumptions=assumptions)
            #except:
               # pass
        # need to have one of the elements positive for the sum to be positive
        raise DeduceInNumberSetException(self, NaturalPos, assumptions)
    """

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        given a number set, attempt to prove that the given expression is in that
        number set using the appropriate closure theorem
        '''
        from proveit.numbers.addition import (
            add_int_closure_bin,
            add_int_closure,
            add_nat_closure_bin,
            add_nat_closure,
            add_nat_pos_closure_bin,
            add_nat_pos_closure,
            add_nat_pos_from_non_neg,
            add_rational_closure_bin,
            add_rational_closure,
            add_rational_non_neg_closure,
            add_rational_non_neg_closure_bin,
            add_rational_pos_closure,
            add_rational_pos_closure_bin,
            add_rational_pos_from_non_neg,
            add_real_closure_bin,
            add_real_closure,
            add_real_non_neg_closure,
            add_real_non_neg_closure_bin,
            add_real_pos_closure,
            add_real_pos_closure_bin,
            add_real_pos_from_non_neg,
            add_complex_closure,
            add_complex_closure_bin)
        from proveit.numbers.addition.subtraction import (
            subtract_nat_closure_bin, sub_one_is_nat)
        from proveit.numbers import (zero, one, Neg, greater,
                                     Less, LessEq, greater_eq)
        from proveit.logic import InSet
        if number_set == Integer:
            if self.operands.is_double():
                return add_int_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_int_closure.instantiate({i:_i, a: _a})
        if number_set == Rational:
            if self.operands.is_double():
                return add_rational_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_rational_closure.instantiate({i: _i, a: _a})
        if number_set == Real:
            if self.operands.is_double():
                return add_real_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_real_closure.instantiate({i: _i, a: _a})
        if number_set == Complex:
            if self.operands.is_double():
                return add_complex_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_complex_closure.instantiate({i: _i, a: _a})
        
        # Prove what we can in preparation.
        for operand in self.operands:
            deduce_number_set(operand)

        # Handle special cases when all operands are in
        # the desired number set.
        if all(InSet(operand, number_set).proven() for
               operand in self.operands):
            if number_set == Natural:
                if self.operands.is_double():
                    return add_nat_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_nat_closure.instantiate({i: _i, a: _a})
            if number_set == NaturalPos:
                if self.operands.is_double():
                    return add_nat_pos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_nat_pos_closure.instantiate({i: _i, a: _a})
            if number_set == RationalPos:
                if self.operands.is_double():
                    return add_rational_pos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_rational_pos_closure.instantiate({i: _i, a: _a})
            if number_set == RationalNonNeg:
                if self.operands.is_double():
                    return add_rational_non_neg_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()
                return add_rational_non_neg_closure.instantiate({i:_i, a: _a})
            if number_set == RealPos:
                if self.operands.is_double():
                    return add_real_pos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                return add_real_pos_closure.instantiate({i: _i, a: _a})
            if number_set == RealNonNeg:
                if self.operands.is_double():
                    return add_real_non_neg_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()
                return add_real_non_neg_closure.instantiate({i:_i, a: _a})

        # Try special case where one term is positive and the
        # rest are non-negative.
        if number_set in {NaturalPos, RationalPos, RealPos}:
            val = None
            for _i, operand in enumerate(self.operands.entries):
                if greater(operand, zero).proven():
                    val = _i
                elif not greater_eq(operand, zero).proven():
                    # Not non-negative
                    val = None
                    break # Forget it.
            if val is not None:
                if number_set == NaturalPos:
                    temp_thm = add_nat_pos_from_non_neg
                elif number_set == RationalPos:
                    temp_thm = add_rational_pos_from_non_neg
                else:
                    temp_thm = add_real_pos_from_non_neg
                _a, _b, _c = (self.operands[:val], self.operands[val],
                              self.operands[val + 1:])
                _i = _a.num_elements()
                _j = _c.num_elements()
                return temp_thm.instantiate(
                    {i: _i, j: _j, a: _a, b: _b, c: _c})

        # Handle positive, negative, nonpos, nonneg, or nonzero
        major_number_set = None
        if number_set in {IntegerNonZero, RationalNonZero, RealNonZero,
                          ComplexNonZero}:
            # Prove it is not zero and prove it is in the corresponding
            # major number set (Integer, Rational, Real, or Complex)
            self.not_equal(zero, try_deduce_number_set=False)
            to_major_number_set = {IntegerNonZero:Integer,
                                   RationalNonZero:Rational,
                                   RealNonZero:Real,
                                   ComplexNonZero:Complex}
            major_number_set = to_major_number_set[number_set]
        if number_set in {NaturalPos, RationalPos, RealPos}:
            # Prove it is positive and prove it is in the corresponding
            # major number set (Integer, Rational, Real)
            self.deduce_positive(try_deduce_number_set=False)
            to_major_number_set = {NaturalPos:Integer,
                                   RationalPos:Rational,
                                   RealPos:Real}
            major_number_set = to_major_number_set[number_set]
        if number_set in {IntegerNeg, RationalNeg, RealNeg}:
            # Prove it is negative and prove it is in the corresponding
            # major number set (Integer, Rational, Real)
            self.deduce_negative(try_deduce_number_set=False)
            to_major_number_set = {IntegerNeg:Integer,
                                   RationalNeg:Rational,
                                   RealNeg:Real}
            major_number_set = to_major_number_set[number_set]
        if number_set in {IntegerNonPos, RationalNonPos, RealNonPos}:
            # Prove it is non-positive and prove it is in the 
            # corresponding major number set (Integer, Rational, Real)
            self.deduce_non_positive(try_deduce_number_set=False)
            to_major_number_set = {IntegerNonPos:Integer,
                                   RationalNonPos:Rational,
                                   RealNonPos:Real}
            major_number_set = to_major_number_set[number_set]
        if number_set in {Natural, RationalNonNeg, RealNonNeg}:
            # Prove it is non-positive and prove it is in the 
            # corresponding major number set (Integer, Rational, Real)
            self.deduce_non_negative(try_deduce_number_set=False)
            to_major_number_set = {Natural:Integer,
                                   RationalNonNeg:Rational,
                                   RealNonNeg:Real}
            major_number_set = to_major_number_set[number_set]

        if major_number_set is not None:
            self.deduce_in_number_set(major_number_set)
            # Now it should just go through.
            return InSet(self, number_set).conclude_as_last_resort()

        raise NotImplementedError(
            "'deduce_in_number_set' on %s not implemented for the %s set"
            % (self, number_set))

    def deduce_positive(self, *, try_deduce_number_set=True,
                        **defaults_config):
        '''
        Prove the sum is positive.
        '''
        from proveit.numbers import greater, zero, Neg
        from .subtraction import pos_difference

        if greater(self, zero).proven():
            # Already known
            return greater(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a > b => (a - b) is positive
            _a, _b = self.terms[0], self.terms[1].operand
            if greater(_a, _b).proven():
                return pos_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        return greater(self, zero).prove()

    @relation_prover
    def deduce_negative(self, *, try_deduce_number_set=True,
                        **defaults_config):
        '''
        Prove the sum is negative.
        '''
        from proveit.numbers import Less, zero, Neg
        from .subtraction import neg_difference

        if Less(self, zero).proven():
            # Already known
            return Less(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a < b => (a - b) is negative
            _a, _b = self.terms[0], self.terms[1].operand
            if Less(_a, _b).proven():
                return neg_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        return Less(self, zero).prove()

    def deduce_non_positive(self, *, try_deduce_number_set=True,
                            **defaults_config):
        '''
        Prove the sum is non-positive.
        '''
        from proveit.numbers import LessEq, zero, Neg
        from .subtraction import nonpos_difference

        if LessEq(self, zero).proven():
            # Already known
            return LessEq(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a <= b => (a - b) is non-positive
            _a, _b = self.terms[0], self.terms[1].operand
            if LessEq(_a, _b).proven():
                return nonpos_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        return LessEq(self, zero).prove()

    def deduce_non_negative(self, *, try_deduce_number_set=True,
                            **defaults_config):
        '''
        Prove the sum is non-negative.
        '''
        from proveit.numbers import greater_eq, zero, Neg
        from .subtraction import nonneg_difference

        if greater_eq(self, zero).proven():
            # Already known
            return greater_eq(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a >= b => (a - b) is non-negative
            _a, _b = self.terms[0], self.terms[1].operand
            if greater_eq(_a, _b).proven():
                return nonneg_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        return greater_eq(self, zero).prove()


    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most 
        restrictive standard number set we can readily know.
        '''
        from proveit.numbers import (Neg, one, greater, greater_eq,
                                     Less, LessEq)
        number_set_map = {
            NaturalPos: NaturalPos,
            IntegerNeg: Integer,
            Natural: Natural,
            IntegerNonPos: Integer,
            IntegerNonZero: Integer,
            Integer: Integer,
            RationalPos: RationalPos,
            RationalNeg: Rational,
            RationalNonNeg: RationalNonNeg,
            RationalNonPos: Rational,
            RationalNonZero: Rational,
            Rational: Rational,
            RealPos: RealPos,
            RealNeg: Real,
            RealNonNeg: RealNonNeg,
            RealNonPos: Real,
            RealNonZero: Real,
            Real: Real,
            ComplexNonZero: Complex,
            Complex: Complex
        }
        
        priorities = {NaturalPos:(0,0), Natural:(0,1), Integer:(0,2),
                      RationalPos:(1,0), RationalNonNeg:(1,1), Rational:(1,2),
                      RealPos:(2,0), RealNonNeg:(2,1), Real:(2,2), 
                      Complex:(3,2)}
        major_minor_to_set = {
            (major, minor):ns for ns, (major, minor) in priorities.items()}
        major_to_nonzero = [IntegerNonZero, RationalNonZero,
                            RealNonZero, ComplexNonZero]
        major_to_nonpos = [IntegerNonPos, RationalNonPos, RealNonPos]
        major_to_neg = [IntegerNeg, RationalNeg, RealNeg]
        
        if self.terms.is_double():
            # Look for a special case of n-1 in Nat or (-1+n) in Nat.
            term_ns = None
            if self.terms[1] == Neg(one):
                term_ns = deduce_number_set(self.terms[0]).domain
            elif self.terms[0] == Neg(one):
                term_ns = deduce_number_set(self.terms[1]).domain         
            if term_ns is not None and NaturalPos.includes(term_ns):
                return self.deduce_in_number_set(Natural)

        major = minor = -1
        any_positive = False
        for term in self.terms:
            term_membership = deduce_number_set(term)
            if isinstance(term, ExprRange):
                # e.g. a_1 in S and ... and a_n in S
                term_ns = term_membership.operands[0].body.domain
            else:
                term_ns = term_membership.domain
            term_ns = number_set_map[term_ns]
            if term_ns in {NaturalPos, RationalPos, RealPos}:
                any_positive = True
            _major, _minor = priorities[term_ns]
            major = max(_major, major)
            minor = max(_minor, minor)
        if major == minor == -1:
            major, minor = 3, 2 # Complex
        elif minor==1 and any_positive:
            # Everything is non-negative and at least one term
            # is positive, so the sum is positive.
            minor = 0

        number_set = None
        # Check for the special case of a - b where we know
        # a > b, a < b, a ≥ b, a ≤ b, or a ≠ b
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            _a, _b = self.terms[0], self.terms[1].operand
            if greater(_a, _b).proven():
                minor = min(0, minor) # positive
            elif greater_eq(_a, _b).proven():
                minor = min(1, minor) # non-negative
            elif Less(_a, _b).proven():
                major = min(major, 2) # must be real
                number_set = major_to_neg[major] # negative
            elif LessEq(_a, _b).proven() and minor==2:
                major = min(major, 2) # must be real
                number_set = major_to_nonpos[major] # non-positive
            elif NotEquals(_a, _b).proven() and minor==2:
                number_set = major_to_nonzero[major] # non-zero

        if number_set is None:
            number_set = major_minor_to_set[(major, minor)]
        return self.deduce_in_number_set(number_set)

    # IS THIS NECESSARY?
    def deduce_difference_in_natural(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Neg
        from proveit.numbers.number_sets.integers import difference_is_nat
        if not self.terms.is_double():
            raise ValueError("deduce_difference_in_natural only applicable "
                             "when there are two terms, got %s" % self)
        if not isinstance(self.terms[1], Neg):
            raise ValueError("deduce_difference_in_natural only applicable "
                             "for a subtraction, got %s" % self)
        thm = difference_is_nat
        return thm.instantiate({a: self.terms[0], b: self.terms[1].operand},
                               assumptions=assumptions)

    # IS THIS NECESSARY?
    def deduce_difference_in_natural_pos(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import Neg
        from proveit.numbers.number_sets.integers import difference_is_nat_pos
        if not self.terms.is_double():
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

    def index(self, the_term, also_return_num=False):
        '''
        Return the starting index of the_term, which may be a single 
        operand, a list of consecutive operands, or a Add expression 
        that represents the sum of the list of consecutive operands.
        If also_return_num is True, return a tuple of the index and 
        number of operands for the_term.
        '''
        if isinstance(the_term, Add):
            the_term = the_term.operands.entries
        if (hasattr(the_term, '__getitem__') and 
                hasattr(the_term, '__len__')):
            # multiple operands in the_term
            first_term = the_term[0]
            num = len(the_term)
            idx = -1
            try:
                while True:
                    idx = self.operands.index(first_term, start=idx + 1)
                    if self.operands[idx:idx + num].entries == tuple(the_term):
                        break  # found it all!
            except ValueError:
                raise ValueError("Term is absent!")
        else:
            num = 1
            try:
                idx = self.operands.index(the_term)
            except ValueError:
                raise ValueError("Term is absent!")
        return (idx, num) if also_return_num else idx

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factors, pull="left", 
                      group_factors=True, group_remainder=True,
                      **defaults_config):
        '''
        Factor out the factor(s) from this sum, pulling it either to 
        the "left" or "right".
        If group_factors is True, the factors are grouped
        together as a sub-product.
        Returns the equality that equates self to this new version.
        '''
        from proveit.numbers.multiplication import distribute_through_sum
        from proveit.numbers import one, Mult
        if pull not in ('left', 'right'):
            raise ValueError("'pull' must be 'left' or 'right'")
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)
        replacements = list(defaults.replacements)
        _b = []
        if not isinstance(the_factors, Expression):
            # If 'the_factors' is not an Expression, assume it is
            # an iterable and make it a Mult.
            the_factors = Mult(*the_factors)
        # factor the_factor from each term
        for _i in range(expr.terms.num_entries()):
            term = expr.terms[_i]
            if hasattr(term, 'factorization'):
                term_factorization = term.factorization(
                    the_factors, pull, group_factors=group_factors,
                    group_remainder=True, preserve_all=True)
                if not isinstance(term_factorization.rhs, Mult):
                    raise ValueError(
                        "Expecting right hand side of each factorization "
                        "to be a product. Instead obtained: {0} for term "
                        "number {1} (0-based index).".
                        format(term_factorization.rhs, _i))
                if pull == 'left':
                    # the grouped remainder on the right
                    _b.append(term_factorization.rhs.operands[-1])
                else:
                    # the grouped remainder on the left
                    _b.append(term_factorization.rhs.operands[0])
                # substitute in the factorized term
                expr = eq.update(term_factorization.substitution(
                    expr.inner_expr().terms[_i], preserve_all=True))
            else:
                if term != the_factors:
                    raise ValueError(
                        "Factor, %s, is not present in the term at "
                        "index %d of %s!" %
                        (the_factors, _i, self))
                if pull == 'left':
                    replacements.append(Mult(term, one).one_elimination(1))
                else:
                    replacements.append(Mult(one, term).one_elimination(0))
                _b.append(one)
        if not group_factors and isinstance(the_factors, Mult):
            factor_sub = the_factors.operands
        else:
            factor_sub = ExprTuple(the_factors)
        if pull == 'left':
            _a = factor_sub
            _c = ExprTuple()
        else:
            _a = ExprTuple()
            _c = factor_sub
        if defaults.auto_simplify:
            # Simplify the remainder of the factorization if
            # auto-simplify is enabled.
            replacements.append(Add(*_b).simplification())
        _b = ExprTuple(*_b)
        _i = _a.num_elements()
        _j = _b.num_elements()
        _k = _c.num_elements()
        distribution = distribute_through_sum.instantiate(
            {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c}, 
            preserve_expr=expr, replacements=replacements)
        eq.update(distribution.derive_reversed())
        return eq.relation

    @equality_prover('commuted', 'commute')
    def commutation(self, init_idx=None, final_idx=None, 
                    **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal 
        to a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, (a + b + ... + y + z) = (a + ... + y + b + z)
        via init_idx = 1 and final_idx = -2.
        '''
        from . import commutation, leftward_commutation, rightward_commutation
        eq = apply_commutation_thm(
            self, init_idx, final_idx, commutation,
            leftward_commutation, rightward_commutation)
        '''
        # DON'T WORRY ABOUT RESETTING THE STYLE FOR THE MOMENT.

        # set the subraction style as appropriate:
        subtraction_positions = self.subtraction_positions()
        eq.inner_expr().lhs.with_subtraction_at(*subtraction_positions)

        eq.inner_expr().rhs.with_subtraction_at(*)
        '''
        return eq

    @equality_prover('group_commuted', 'group_commute')
    def group_commutation(self, init_idx, final_idx, length,
                          disassociate=True, **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal
        to a form in which the operands at indices 
        [init_idx, init_idx+length) have been moved to 
        [final_idx. final_idx+length).
        It will do this by performing association first.  
        If disassocate is True, it will be disassociated afterwards.
        '''
        return group_commutation(
            self, init_idx, final_idx, length, disassociate=disassociate)

    @equality_prover('associated', 'associate')
    def association(self, start_idx, length, **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal 
        to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (a + b + ... + y + z) = 
            (a + b ... + (l + ... + m) + ... + y + z)
        '''
        from . import association
        eq = apply_association_thm(
            self, start_idx, length, association)

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

    @equality_prover('disassociated', 'disassociate')
    def disassociation(self, idx, **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal 
        to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a + b ... + (l + ... + m) + ... + y+ z) 
            = (a + b + ... + y + z)
        '''
        from proveit.core_expr_types import Len
        from proveit.numbers import Neg
        from . import disassociation
        from .subtraction import subtraction_disassociation

        if (isinstance(self.operands[idx], Neg) and
                isinstance(self.operands[idx].operand, Add)):
            subtraction_terms = self.operands[idx].operand.operands
            _a = self.operands[:idx]
            _b = subtraction_terms
            _c = self.operands[idx + 1:]
            _i = Len(_a).computed()
            _j = Len(_b).computed()
            _k = Len(_c).computed()
            return subtraction_disassociation.instantiate(
                {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c})
        eq = apply_disassociation_thm(self, idx, disassociation)
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

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        Alias for bound_via_term_bound.
        Also see NumberOperation.deduce_bound.
        '''
        return self.bound_via_term_bound(operand_relation)

    @relation_prover
    def bound_via_term_bound(self, term_relation, **defaults_config):
        '''
        Deduce a bound of this sum via the bound on
        one of its terms.  For example
            a + b + c + d < a + z + c + d   given   b < z.

        Also see NumberOperation.deduce_bound.            
        '''
        from proveit.numbers import NumberOrderingRelation, Less
        if isinstance(term_relation, Judgment):
            term_relation = term_relation.expr
        if not isinstance(term_relation, NumberOrderingRelation):
            raise TypeError("'term_relation' expected to be a number "
                            "relation (<, >, ≤, or ≥)")
        idx = None
        for side in term_relation.operands:
            try:
                idx, num = self.index(side, also_return_num=True)
                break
            except ValueError:
                pass
        if idx is None:
            raise TypeError("'term_relation' expected to be a relation "
                            "for one of the terms; neither term of %s "
                            "appears in the %s relation."
                            %(self, term_relation))
        expr = self
        eq = TransRelUpdater(expr)
        if num > 1:
            expr = eq.update(expr.association(idx, num,))
        if expr.operands.is_double():
            # Handle the binary cases.
            assert 0 <= idx < 2
            if idx == 0:
                relation = term_relation.right_add_both_sides(expr.terms[1])
            elif idx == 1:
                relation = term_relation.left_add_both_sides(expr.terms[0])
            expr = eq.update(relation)
        else:
            thm = None
            if isinstance(term_relation, Less):
                # We can use the strong bound.
                from . import strong_bound_via_term_bound
                thm = strong_bound_via_term_bound
            else:
                # We may only use the weak bound.
                from . import weak_bound_via_term_bound
                thm = weak_bound_via_term_bound
            _a = self.terms[:idx]
            _b = self.terms[idx+1:]
            _i = _a.num_elements()
            _j = _b.num_elements()
            _x = term_relation.normal_lhs
            _y = term_relation.normal_rhs
            expr = eq.update(thm.instantiate(
                    {i: _i, j: _j, a: _a, b: _b, x: _x, y: _y}))
        if num > 1 and isinstance(expr.terms[idx], Add):
            expr = eq.update(expr.disassociation(idx))            
        relation = eq.relation
        if relation.lhs != self:
            relation = relation.with_direction_reversed()
        assert relation.lhs == self
        return relation    

    @relation_prover
    def bound_by_term(self, term_or_idx, use_weak_bound=False,
                      **defaults_config):
        '''
        Deduce that this sum is bound by the given term (or term at
        the given index).
        
        For example,
        a + b + c + d ≥ b provided that a ≥ 0, c ≥ 0, and d ≥ 0.
        
        To use this method, we must know that the
        other terms are all in RealPos, RealNeg, RealNonNeg, or
        RealNonPos and will call
        deduce_weak_upper_bound_by_term,
        deduce_strong_upper_bound_by_term,
        deduce_weak_lower_bound_by_term,
        deduce_strong_lower_bound_by_term
        accordingly.
        '''
        from proveit.numbers import RealPos, RealNeg, RealNonNeg, RealNonPos
        relevant_number_sets = {RealPos, RealNeg, RealNonNeg, RealNonPos}
        for _k, term_entry in enumerate(self.terms.entries):
            if _k == term_or_idx or term_entry == term_or_idx: 
                # skip the term doing the bounding.
                continue
            for number_set in list(relevant_number_sets):
                deduce_number_set(term_entry)
                if isinstance(term_entry, ExprRange):
                    in_number_set = And(ExprRange(
                            term_entry.parameter,
                            InSet(term_entry.body, number_set),
                            term_entry.true_start_index, 
                            term_entry.true_end_index))
                else:
                    in_number_set = InSet(term_entry, number_set)
                if not in_number_set.proven():
                    relevant_number_sets.discard(number_set)
        if len(relevant_number_sets) == 0:
            raise UnsatisfiedPrerequisites(
                    "In order to use Add.bound_by_term, the "
                    "'other' terms must all be known to be contained "
                    "in RealPos, RealNeg, RealNonNeg, RealNonPos")
        if not use_weak_bound:
            # If a strong bound is applicable, use that.
            if RealPos in relevant_number_sets:
                return self.deduce_strong_lower_bound_by_term(term_or_idx)
            if RealNeg in relevant_number_sets:
                return self.deduce_strong_upper_bound_by_term(term_or_idx)
        if RealNonNeg in relevant_number_sets:
            return self.deduce_weak_lower_bound_by_term(term_or_idx)
        if RealNonPos in relevant_number_sets:
            return self.deduce_weak_upper_bound_by_term(term_or_idx)

    @relation_prover
    def deduce_weak_lower_bound_by_term(
            self, term_or_idx, **defaults_config):
        '''
        Deduce that this sum is greater than or equal to the term at the
        given index.
        '''
        from . import term_as_weak_lower_bound
        return self._deduce_specific_bound_by_term(
                term_as_weak_lower_bound, term_or_idx)

    @relation_prover
    def deduce_weak_upper_bound_by_term(
            self, term_or_idx, **defaults_config):
        '''
        Deduce that this sum is less than or equal to the term at the
        given index.
        '''
        from . import term_as_weak_upper_bound
        return self._deduce_specific_bound_by_term(
                term_as_weak_upper_bound, term_or_idx)

    @relation_prover
    def deduce_strong_lower_bound_by_term(
            self, term_or_idx, **defaults_config):
        '''
        Deduce that this sum is greater than the term at the
        given index.
        '''
        from . import term_as_strong_lower_bound
        return self._deduce_specific_bound_by_term(
                term_as_strong_lower_bound, term_or_idx)

    @relation_prover
    def deduce_strong_upper_bound_by_term(
            self, term_or_idx, **defaults_config):
        '''
        Deduce that this sum is less than the term at the
        given index.
        '''
        from . import term_as_strong_upper_bound
        return self._deduce_specific_bound_by_term(
                term_as_strong_upper_bound, term_or_idx)

    def _deduce_specific_bound_by_term(self, thm, term_or_idx):
        '''
        Helper method for 
        deduce_weak_lower_bound_by_term,
        deduce_weak_upper_bound_by_term, 
        deduce_strong_lower_bound_by_term, and 
        deduce_strong_lower_bound_by_term.
        '''
        if isinstance(term_or_idx, Expression):
            try:
                idx = self.terms.index(term_or_idx)
            except ValueError:
                raise ValueError(
                        "'term_or_idx' must be one of the terms of %s "
                        "or an index for one of the terms."%self)
        else:
            if not isinstance(term_or_idx, int):
                raise TypeError(
                        "'term_or_idx' must be an Expression or int")
            idx = term_or_idx
        _a = self.terms[:idx]
        _b = self.terms[idx]
        _c = self.terms[idx + 1:]
        _i = _a.num_elements()
        _j = _c.num_elements()
        return thm.instantiate({i: _i, j: _j, a: _a, b: _b, c: _c})        

    @relation_prover
    def not_equal(self, other, *, try_deduce_number_set=True,
                  **defaults_config):
        '''
        Attempt to prove that self is not equal to other.
        '''
        from proveit.numbers import zero, Neg
        if NotEquals(self, other).proven():
            # Already known.
            return NotEquals(self, other).prove()
        if other == zero:
            if self.terms.is_double():
                if isinstance(self.terms[1], Neg):
                    from .subtraction import nonzero_difference_if_different
                    _a = self.terms[0]
                    _b = self.terms[1].operand
                    #if (NotEquals(_a, _b).proven(assumptions) and
                    #        nonzero_difference_if_different.is_usable()):
                    if nonzero_difference_if_different.is_usable():
                        # If we know that _a ≠ _b then we can 
                        # prove _a - _b ≠ 0.
                        return nonzero_difference_if_different.instantiate(
                                {a:_a, b:_b})
            if try_deduce_number_set:
                # Try deducing the number set.
                deduce_number_set(self)
                if NotEquals(self, zero).proven():
                    return NotEquals(self, zero).prove()
        # If it isn't a special case treated here, just use
        # conclude-as-folded.
        return NotEquals(self, other).conclude_as_folded()

def subtract(a, b):
    '''
    Return the a-b expression (which is internally a+(-b)).
    '''
    from proveit.numbers import Neg
    if isinstance(b, ExprRange):
        b = ExprRange(b.lambda_map.parameter_or_parameters,
                      Neg(b.lambda_map.body), b.true_start_index,
                      b.true_end_index, b.get_styles())
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
                            Neg(b.lambda_map.body), b.true_start_index,
                            b.true_end_index, b.get_styles())]
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

def split_int_shift(expr):
    '''
    If the expression contains an additive integer shift term,
    return the remaining terms and the shift independently as a pair.
    Otherwise, return the expression paired with a zero shift.
    '''
    from proveit.numbers import is_literal_int, zero, Neg
    if isinstance(expr, Neg):
        expr = Add(expr) # wrap in an Add so we can do quick_simplified
    if isinstance(expr, Add):
        expr = expr.quick_simplified()
        if (isinstance(expr, Add) and is_literal_int(expr.terms[-1])):
            shift = expr.terms[-1].as_int()
            if expr.terms.num_entries() == 1:
                return shift
            elif (expr.terms.num_entries() == 2 and 
                    not isinstance(expr.terms[0], ExprRange)):
                return expr.terms[0], shift
            else:
                return Add(expr.terms[:-1]), shift
    if is_literal_int(expr):
        return zero, expr.as_int()
    return expr, 0
