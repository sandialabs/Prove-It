import math
import bisect
from collections import deque, Counter

from proveit import (Expression, Judgment, Literal, Operation, ExprTuple,
                     ExprRange, defaults, StyleOptions, 
                     prover, relation_prover, equality_prover,
                     auto_prover, auto_relation_prover, auto_equality_prover,
                     maybe_fenced_latex, ProofFailure, InnerExpr,
                     UnsatisfiedPrerequisites,
                     SimplificationDirectives, TransRelUpdater)
from proveit.util import OrderedSet
from proveit import a, b, c, d, e, i, j, k, l, n, x, y, free_vars
from proveit.logic import (And, Equals, NotEquals,
                           EvaluationError, InSet)
from proveit.logic.irreducible_value import is_irreducible_value
from proveit.numbers import (NumberOperation, standard_number_set,
                             pos_number_set, neg_number_set, 
                             nonneg_number_set, nonpos_number_set,
                             nonzero_number_set,
                             union_number_set, deduce_number_set,
                             readily_provable_number_set)
from proveit.numbers.numerals.decimals import DIGITS
import proveit.numbers.numerals.decimals
from proveit.abstract_algebra.generic_methods import (
        apply_commutation_thm, apply_association_thm, 
        apply_disassociation_thm, group_commutation, pairwise_evaluation,
        deduce_equality_via_commutation, generic_permutation,
        sorting_operands, sorting_and_combining_like_operands,
        common_likeness_key)
from proveit import TransRelUpdater
from proveit.numbers import (ZeroSet, Integer, IntegerNeg, IntegerNonPos,
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
            combine_like_terms = True,
            order_key_fn = lambda term : 0)

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
        If the right side is irreducible and the left side is
        binary, a + b = c, derive the commutation
            b + a = c
        and if neither a nor b is a Neg, also derive the following:
            -a - b = -c
            c - b = a
            b - c = -a
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

    def _build_canonical_form(self):
        '''
        Returns a form of this Add with operands in their canonical 
        forms, nested addition is ungrouped, and "common" terms that 
        are the same except coefficient factors are combined, and 
        these terms are all ordered deterministically according to
        hash values of the non-coefficient parts of the terms.
        
        Example: (2/3)*a*b + c + 1 - (-1/4)*a*b + c + (1/3) ->
                 (4/3) + (11/12) a*b + 2 c
        The order of the terms is arbitrary but deterministic
        (sorted by hash value).
        '''
        from proveit.numbers import (zero, one, Neg, Mult,
                                     is_numeric_rational,
                                     numeric_rational_ints,
                                     simplified_numeric_rational)
        from proveit.numbers.multiplication.mult import (
                coefficient_and_remainder)
        if self.terms.num_entries() == 0:
            return zero # Add operation with no operands
        remainder_to_rational_coef = dict()
        contains_only_numeric_rationals = True
        # Generate canonical forms of terms and ungroup nested
        # addition:
        def gen_coef_and_remainders(expr):
            for term in expr.terms:
                canonical_term = term.canonical_form()
                if isinstance(canonical_term, Neg):
                    # Negation should distribute through Add
                    # in its canonical form.
                    assert not isinstance(canonical_term.operand, Add)
                if isinstance(canonical_term, Add):
                    for _coeff_and_remainder in gen_coef_and_remainders(
                            canonical_term):
                        yield _coeff_and_remainder
                    # for sub_term in canonical_term.terms:
                    #     yield coefficient_and_remainder(sub_term)
                elif isinstance(canonical_term, ExprRange):
                    yield (one, Add(canonical_term))
                else:
                    yield coefficient_and_remainder(canonical_term)
        for coef, remainder in gen_coef_and_remainders(self):
            if coef == zero:
                continue
            if remainder != one:
                contains_only_numeric_rationals = False
            if remainder in remainder_to_rational_coef:
                prev_coef = remainder_to_rational_coef[remainder]
                if isinstance(prev_coef, Add):
                    remainder_to_rational_coef[remainder] = Add(
                            *prev_coef.terms.entries, coef)
                else:
                    remainder_to_rational_coef[remainder] = Add(
                            prev_coef, coef)
            else:
                remainder_to_rational_coef[remainder] = coef
        if len(remainder_to_rational_coef) == 0:
            return zero # Add() = 0
        if len(remainder_to_rational_coef) == 1:
            # special case to avoid infinite recursion
            remainder, coeff = next(iter(remainder_to_rational_coef.items()))
            if coeff == one:
                return remainder
        if contains_only_numeric_rationals:
            # This is a sum of only numeric rationals.  Just
            # compute it.
            assert len(remainder_to_rational_coef)==1
            assert one in remainder_to_rational_coef
            expr = remainder_to_rational_coef[one]
            if not isinstance(expr, Add):
                assert is_numeric_rational(expr)
                return expr
            sum_as_expr = zero
            for term in expr.terms:
                # Add to the cumulative sum.
                # (a/b) + (c/d) = (a*d + c*b)/(b*d)
                _a, _b = numeric_rational_ints(sum_as_expr)
                _c, _d = numeric_rational_ints(term)
                sum_as_expr = simplified_numeric_rational(_a*_d+_c*_b, _b*_d)
            return sum_as_expr
        terms = []
        for remainder in sorted(remainder_to_rational_coef.keys(), key=hash):
            if remainder==one: 
                # We'll save the constant (numeric rational) for the
                # last term (consistent with the 'quick simplified' 
                # form).
                continue
            coef = remainder_to_rational_coef[remainder].canonical_form()
            if coef == zero: continue
            if coef == one:
                term = remainder
            elif isinstance(remainder, Mult):
                term = Mult(coef, *remainder.factors.entries)
            else:
                term = Mult(coef, remainder)
            canonical_term = term.canonical_form()
            terms.append(canonical_term)
        if one in remainder_to_rational_coef:
            # Add the numeric rational as the last term.
            coef = remainder_to_rational_coef[one].canonical_form()
            if coef != zero: terms.append(coef)
        if len(terms) == 0:
            return zero
        elif len(terms) == 1:
            return terms[0]
        else:
            return Add(*terms)
        
        return Add(*sorted([operand.canonical_form() for operand 
                           in self.operands.entries], key=hash))

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
        operands = self.operands
        if (operands.num_entries() == 1 
                and isinstance(operands[0], ExprRange)
                and operands[0].is_parameter_independent):
            expr_range = operands[0]
            replacements = []
            start_index = operands[0].true_start_index
            if start_index != one:
                # change the indexing to start from 1.
                replacement = operands[0].shift_equivalence(
                        new_start=one).derive_reversed()
                _n = replacement.rhs.entries[0].true_end_index
                replacements.append(replacement)
            else:
                _n = expr_range.true_end_index
            # x + x + ..(n-3)x.. + x = x*n
            return repeated_addition_to_mult.instantiate(
                {x: expr_range.body, n: _n},
                replacements=replacements)
        # Obtain the first element; all other elements should equal
        # this.
        for operand in operands:
            if isinstance(operand, ExprRange):
                _x = operand.first()
            else:
                _x = operand
        _n = operands.num_elements()
        _a = operands
         # a1 + a2 + ..(n-3)x.. + an = x*n if each a1,a2,..,an equals x.
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
                neg_operand_indices.setdefault(
                        operand.operand.canonical_form(), 
                        OrderedSet()).add(_i)

        canceled_indices = []
        for _i, operand in enumerate(self.operands.entries):
            if isinstance(operand, Neg):
                continue
            operand_cf = operand.canonical_form()
            if operand_cf in neg_operand_indices:
                indices = neg_operand_indices[operand_cf]
                _j = indices.pop()
                if len(indices) == 0:
                    # no more indices to use in the future
                    neg_operand_indices.pop(operand_cf)
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
        import proveit.numbers.addition.subtraction as sub_pkg
        from proveit.numbers import Neg
        if idx1 > idx2:
            # choose i to be less than j
            return self.cancelation(idx2, idx1)

        if isinstance(self.operands[idx2], Neg):
            basic_thm = sub_pkg.add_cancel_basic
            triple_thms = (
                sub_pkg.add_cancel_triple_12,
                sub_pkg.add_cancel_triple_13,
                sub_pkg.add_cancel_triple_23)
            general_thm = sub_pkg.add_cancel_general
            _a = self.operands[idx1]
            _b = self.operands[idx2].operand
        elif isinstance(self.operands[idx1], Neg):
            basic_thm = sub_pkg.add_cancel_reverse
            triple_thms = (
                sub_pkg.add_cancel_triple_21,
                sub_pkg.add_cancel_triple_31,
                sub_pkg.add_cancel_triple_32)
            general_thm = sub_pkg.add_cancel_general_rev
            _a = self.operands[idx1].operand
            _b = self.operands[idx2]
        else:
            raise ValueError("Unable to cancel %s and %s; "
                             "neither is in an explicitly negated form."
                             %(self.operands[idx1], self.operands[idx2]))

        if self.operands.is_double():
            return basic_thm.instantiate({a:_a, b:_b})
        elif (not self.operands.contains_range() 
                and self.operands.num_entries() == 3):
            # _k is the 3rd index, completing i and j in the set {0,1,2}.
            _k = {0, 1, 2}.difference([idx1, idx2]).pop()
            thm = triple_thms[2 - _k]
            return thm.instantiate({a:_a, b:_b, c: self.operands[_k]})
        else:
            _b, _d = _a, _b
            _a = self.operands[:idx1]
            _c = self.operands[idx1 + 1:idx2]
            _e = self.operands[idx2 + 1:]
            _i = _a.num_elements()
            _j = _c.num_elements()
            _k = _e.num_elements()
            return general_thm.instantiate(
                {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c, d: _d, e: _e})

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
        from proveit.numbers import (one, Add, Neg, Mult, 
                                     is_numeric_int,
                                     is_numeric_rational)
        from proveit.numbers.multiplication.mult import (
                coefficient_and_remainder)
        from . import empty_addition, unary_add_reduction
        
        if self.operands.num_entries() == 0:
            # [+]() = 0
            return empty_addition
        
        if self.operands.is_single():
            return unary_add_reduction.instantiate({a:self.operands[0]},
                                                    preserve_all=True)

        # If all operands are negated, factor out the negation.
        if all(isinstance(operand, Neg) for operand in self.operands):
            negated = Neg(
                Add(*[operand.operand for operand in self.operands]))
            neg_distribution = negated.distribution(auto_simplify=False)
            neg_factored = neg_distribution.derive_reversed()
            return neg_factored.inner_expr().rhs.simplify()
        
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
                if (isinstance(operand, Add) or
                        (isinstance(operand, Neg) and
                         isinstance(operand.operand, Add))):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, preserve_all=True))
                length = expr.operands.num_entries()
                _n += 1
        
        # See if there are any parameter-independent expression
        # ranges to be converted to multiplication:
        #  x + x + ..(n-3)x.. + x = x*n
        for _k, operand in enumerate(expr.operands):
            if isinstance(operand, ExprRange) and (
                    operand.is_parameter_independent):
                if expr.operands.num_entries():
                    return expr.conversion_to_multiplication(
                            preserve_expr=operand.body, auto_simplify=True)
                expr_range_term = Add(expr.operands[_k])
                replacement = expr_range_term.conversion_to_multiplication(
                        preserve_expr=operand.body, auto_simplify=True)
                expr = eq.update(expr.inner_expr().associated(
                        _k, 1, replacements=[replacement]))

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

        # If all operands are irreducible, perform the evaluation.
        terms = self.terms
        if all(is_irreducible_value(term) for term in terms):
            if self.operands.is_double():                
                if all(is_numeric_int(term) for term in terms):
                    # Evaluate the addition of two literal integers.
                    evaluation = self._integer_binary_eval()
                    return evaluation
                elif all(is_numeric_rational(term) for term in terms):
                    # Evaluate the addition of two literal rationals.
                    evaluation = self._rational_binary_eval()
                    return evaluation
                else:
                    # In the future, handle adding irreducible
                    # complex numbers and/or irrationals as
                    # appropriate.
                    pass
            else:
                # Do a pairwise addition of irreducible terms.         
                return pairwise_evaluation(self)

        order_key_fn = Add._simplification_directives_.order_key_fn
        if Add._simplification_directives_.combine_like_terms and (
                not must_evaluate):
            # Like terms are ones whose that are the same
            # apart from literal, rational coefficients.
            likeness_key_fn = lambda term : (
                    coefficient_and_remainder(term)[1])
            # Sort and combine like operands.
            expr = eq.update(sorting_and_combining_like_operands(
                    expr, order_key_fn=order_key_fn, 
                    likeness_key_fn=likeness_key_fn,
                    preserve_likeness_keys=True, auto_simplify=True))
        else:
            # See if we should reorder the terms.
            expr = eq.update(sorting_operands(expr, order_key_fn=order_key_fn,
                                              auto_simplify=False))
        
        if expr != self:
            # Try starting over with a call to shallow_simplification
            # (an evaluation may already be known).
            eq.update(expr.shallow_simplification(
                    must_evaluate=must_evaluate))
            return eq.relation

        if all(is_irreducible_value(term) for term in self.terms):
            raise NotImplementedError(
                "Addition evaluation only implemented for rationals: %s"
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
        nested additions are ungrouped, integers are extracted,
        added, and placed at the end, and cancelations are made on
        individual terms as well as expression ranges or portions of
        expression ranges.  We freely assume terms represent numbers
        and expression ranges are well-formed.
        This quick-n-dirty approach can be good
        enough for the purposes of displaying expressions involving
        expression ranges.  See also the quick_simplified_index 
        function defined in number_operation.py.
        '''
        from proveit.numbers import is_numeric_int, num, Neg
        
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
        
        def expandable_range(term):
            if not isinstance(term, ExprRange):
                return False
            # Currently this doesn't expand ExprRange bodies that
            # are Add or Neg which would themselves be expanded.
            # This algorithm needs to be redesigned to handle such
            # fancy cases.
            if isinstance(term.body, Add) or  isinstance(term.body, Neg):
                return False
            return True
            
        while len(remaining_terms):
            term = remaining_terms.popleft()
            if term == Neg:
                # Just an indication to switch the sign back.
                sign = -sign
                continue
            if is_numeric_int(term):
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
            if expandable_range(term):
                start_base, start_shift = split_int_shift(
                        term.true_start_index)
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
                if expandable_range(abs_term):
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
                            and expandable_range(following_term[1])):
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
                            expandable_range(prev_term[1])):
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

    def _integer_binary_eval(self):
        '''
        Evaluate the sum of possibly negated single digit numbers.
        '''
        from proveit.numbers import is_numeric_int, num
        from proveit.numbers.numerals import DecimalSequence
        terms = self.terms
        assert terms.is_double()
        assert all(is_numeric_int(term) for term in terms)
        _a, _b = terms
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
        if not all(term in DIGITS for term in (num(_a), num(_b))):
            # multi-digit addition
            return DecimalSequence.add_eval(_a, _b)
        with defaults.temporary() as temp_defaults:
            # We rely upon side-effect automation here.
            temp_defaults.sideeffect_automation = True
            # for single digit addition, import the theorem that provides
            # the evaluation
            proveit.numbers.numerals.decimals.__getattr__(
                    'add_%d_%d' % (_a, _b))
        return self.evaluation()

    def _rational_binary_eval(self):
        '''
        Evaluate the sum of possibly literal rational numbers.
        The evaluation must be irreducible which means that the result
        (right hand side of the proven equation) must be an integer
        or a (possibly negated) fraction with no common divisors between
        the numerator and denominator other than 1.
        '''
        from proveit.numbers import (Div, num, is_numeric_rational, 
                                     numeric_rational_ints)
        from . import rational_pair_addition
        terms = self.terms
        if not terms.is_double() or (
                not all(is_numeric_rational(term) for term in terms)):
            raise ValueError(
                "_rational_binary_eval only applicable for binary addition "
                "of rationals")
        _a, _b = numeric_rational_ints(terms[0])
        _c, _d = numeric_rational_ints(terms[1])
        _a, _b, _c, _d = num(_a), num(_b), num(_c), num(_d)
        # Replace the irreducible forms with the original forms.
        replacements = [Equals(Div(_a, _b), terms[0]).prove(),
                        Equals(Div(_c, _d), terms[1]).prove()]

        # Combine the sum using
        #   (a/b) + (c/d) = (a*d + b*c)/(b*d)
        # Applying automatic simplifications should evaluate the
        # numerator and denominator and then reduce it to an
        # irreducible form.
        return rational_pair_addition.instantiate(
                {a:_a, b:_b, c:_c, d:_d}, 
                auto_simplify=True, replacements=replacements,
                preserve_expr=self)

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
        import proveit.numbers.addition as add_pkg
        from proveit.numbers.addition.subtraction import (
            subtract_nat_closure_bin, sub_one_is_nat)
        from proveit.numbers import (zero, one, Neg, greater,
                                     Less, LessEq, greater_eq)
        from proveit.logic import InSet
        
        if number_set == ZeroSet:
            if self.operands.is_double():
                return add_pkg.add_zero_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_pkg.add_zero_closure.instantiate({i:_i, a: _a})
        if number_set == Integer:
            if self.operands.is_double():
                return add_pkg.add_int_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_pkg.add_int_closure.instantiate({i:_i, a: _a})
        if number_set == Rational:
            if self.operands.is_double():
                return add_pkg.add_rational_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_pkg.add_rational_closure.instantiate({i: _i, a: _a})
        if number_set == Real:
            if self.operands.is_double():
                return add_pkg.add_real_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_pkg.add_real_closure.instantiate({i: _i, a: _a})
        if number_set == Complex:
            if self.operands.is_double():
                return add_pkg.add_complex_closure_bin.instantiate(
                    {a: self.operands[0], b: self.operands[1]})
            _a = self.operands
            _i = _a.num_elements()
            return add_pkg.add_complex_closure.instantiate({i: _i, a: _a})
        
        # Prove what we can in preparation.
        for operand in self.operands:
            deduce_number_set(operand)

        # Handle special cases when all operands are in
        # the desired number set.
        if all(InSet(operand, number_set).proven() for
               operand in self.operands):
            if number_set == Natural:
                if self.operands.is_double():
                    return add_pkg.add_nat_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_pkg.add_nat_closure.instantiate({i: _i, a: _a})
            if number_set == NaturalPos:
                if self.operands.is_double():
                    return add_pkg.add_nat_pos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_pkg.add_nat_pos_closure.instantiate({i: _i, a: _a})
            if number_set == IntegerNeg:
                if self.operands.is_double():
                    return add_pkg.add_int_neg_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_pkg.add_int_neg_closure.instantiate({i: _i, a: _a})
            if number_set == IntegerNonPos:
                if self.operands.is_double():
                    return add_pkg.add_int_nonpos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_pkg.add_int_nonpos_closure.instantiate({i: _i, a: _a})
            if number_set == RationalPos:
                if self.operands.is_double():
                    return add_pkg.add_rational_pos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_pkg.add_rational_pos_closure.instantiate({i: _i, a: _a})
            if number_set == RationalNeg:
                if self.operands.is_double():
                    return add_pkg.add_rational_neg_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                add_pkg.add_rational_neg_closure.instantiate({i: _i, a: _a})
            if number_set == RationalNonNeg:
                if self.operands.is_double():
                    return add_pkg.add_rational_nonneg_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()
                return add_pkg.add_rational_nonneg_closure.instantiate({i:_i, a: _a})
            if number_set == RationalNonPos:
                if self.operands.is_double():
                    return add_pkg.add_rational_nonpos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()
                return add_pkg.add_rational_nonpos_closure.instantiate({i:_i, a: _a})
            if number_set == RealPos:
                if self.operands.is_double():
                    return add_pkg.add_real_pos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                return add_pkg.add_real_pos_closure.instantiate({i: _i, a: _a})
            if number_set == RealNeg:
                if self.operands.is_double():
                    return add_pkg.add_real_neg_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()                
                return add_pkg.add_real_neg_closure.instantiate({i: _i, a: _a})
            if number_set == RealNonNeg:
                if self.operands.is_double():
                    return add_pkg.add_real_nonneg_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()
                return add_pkg.add_real_nonneg_closure.instantiate({i:_i, a: _a})
            if number_set == RealNonPos:
                if self.operands.is_double():
                    return add_pkg.add_real_nonpos_closure_bin.instantiate(
                        {a: self.operands[0], b: self.operands[1]})
                _a = self.operands
                _i = _a.num_elements()
                return add_pkg.add_real_nonpos_closure.instantiate({i:_i, a: _a})

        # Try special case where one term is positive and the
        # rest are non-negative.
        if number_set in {NaturalPos, RationalPos, RealPos}:
            val = None
            for _i, operand in enumerate(self.operands.entries):
                if greater(operand, zero).readily_provable():
                    val = _i
                elif not greater_eq(operand, zero).readily_provable():
                    # Not non-negative
                    val = None
                    break # Forget it.
            if val is not None:
                if number_set == NaturalPos:
                    temp_thm = add_pkg.add_nat_pos_from_nonneg
                elif number_set == RationalPos:
                    temp_thm = add_pkg.add_rational_pos_from_nonneg
                else:
                    temp_thm = add_pkg.add_real_pos_from_nonneg
                _a, _b, _c = (self.operands[:val], self.operands[val],
                              self.operands[val + 1:])
                _i = _a.num_elements()
                _j = _c.num_elements()
                return temp_thm.instantiate(
                    {i: _i, j: _j, a: _a, b: _b, c: _c})
        # Try special case where one term is negative and the
        # rest are non-positive.
        if number_set in {IntegerNeg, RationalNeg, RealNeg}:
            val = None
            for _i, operand in enumerate(self.operands.entries):
                if greater(operand, zero).readily_provable():
                    val = _i
                elif not greater_eq(operand, zero).readily_provable():
                    # Not non-negative
                    val = None
                    break # Forget it.
            if val is not None:
                if number_set == NaturalPos:
                    temp_thm = add_pkg.add_int_neg_from_nonpos
                elif number_set == RationalPos:
                    temp_thm = add_pkg.add_rational_neg_from_nonpos
                else:
                    temp_thm = add_pkg.add_real_neg_from_nonpos
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
            self.deduce_not_equal(zero, try_deduce_number_set=False)
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
            # Already known (don't use readily_provable).
            return greater(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a > b => (a - b) is positive
            _a, _b = self.terms[0], self.terms[1].operand
            if greater(_a, _b).readily_provable():
                return pos_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        # Last resort attempt
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
            # Already known (don't use readily_provable).
            return Less(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a < b => (a - b) is negative
            _a, _b = self.terms[0], self.terms[1].operand
            if Less(_a, _b).readily_provable():
                return neg_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        # Last resort attempt
        return Less(self, zero).prove()

    def deduce_non_positive(self, *, try_deduce_number_set=True,
                        **defaults_config):
        '''
        Prove the sum is non-positive.
        '''
        from proveit.numbers import LessEq, zero, Neg
        from .subtraction import nonpos_difference

        if LessEq(self, zero).proven():
            # Already known (don't use readily_provable).
            return LessEq(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a <= b => (a - b) is non-positive
            _a, _b = self.terms[0], self.terms[1].operand
            if LessEq(_a, _b).readily_provable():
                return nonpos_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        # Last resort attempt
        return LessEq(self, zero).prove()

    def deduce_non_negative(self, *, try_deduce_number_set=True,
                            **defaults_config):
        '''
        Prove the sum is non-negative.
        '''
        from proveit.numbers import greater_eq, zero, Neg
        from .subtraction import nonneg_difference

        if greater_eq(self, zero).proven():
            # Already known (don't use readily_provable).
            return greater_eq(self, zero).prove()
        
        if self.terms.is_double() and isinstance(self.terms[1], Neg):
            # (a - b) with a >= b => (a - b) is non-negative
            _a, _b = self.terms[0], self.terms[1].operand
            if greater_eq(_a, _b).readily_provable():
                return nonneg_difference.instantiate({a:_a, b:_b})

        if try_deduce_number_set:
            # Try 'deduce_number_set'.
            deduce_number_set(self)

        # Last resort attempt
        return greater_eq(self, zero).prove()

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        from proveit.numbers import (Neg, greater, greater_eq,
                                     Less, LessEq)
        nonzero_to_full_number_set = {
                IntegerNonZero:Integer,
                RationalNonZero:Rational,
                RealNonZero:Real,
                ComplexNonZero:Complex}
        operands = self.operands
        if operands.num_entries() == 0:
            return ZeroSet # [+]() = 0
        list_of_operand_sets = []
        # find a minimal std number set for operand
        any_positive = False
        any_negative = False
        for operand in operands:
            operand_ns = readily_provable_number_set(operand)
            if RealPos.readily_includes(operand_ns):
                any_positive = True
            if RealNeg.readily_includes(operand_ns):
                any_negative = True
            list_of_operand_sets.append(operand_ns)
        # Find the number set that 
        number_set = union_number_set(*list_of_operand_sets)
        
        if number_set in nonzero_to_full_number_set:
            # Adding non-zero operands provides no guarantee that the
            # result will be non-zero (unlike adding positives,
            # negatives, nonpositives, or nonnegatives).
            number_set = nonzero_to_full_number_set[number_set]

        restriction = None
        if RealPos.readily_includes(number_set):
            restriction = pos_number_set # must be positive
        elif RealNeg.readily_includes(number_set):
            restriction = neg_number_set # must be negative
        elif RealNonNeg.readily_includes(number_set):
            if any_positive:
                restriction = pos_number_set # must be positive
            else:
                restriction = nonneg_number_set # must be non-negative
        elif RealNonPos.readily_includes(number_set):
            if any_negative:
                restriction = neg_number_set # must be negative
            else:
                restriction = nonpos_number_set # must be non-positive

        if restriction not in (pos_number_set, neg_number_set):
            # Check for the special case of a - b where we know
            # a > b, a < b, a ≥ b, a ≤ b, or a ≠ b
            if self.terms.is_double() and isinstance(self.terms[1], Neg):
                _a, _b = self.terms[0], self.terms[1].operand
                if greater(_a, _b).readily_provable():
                    restriction = pos_number_set # positive
                elif greater_eq(_a, _b).readily_provable():
                    restriction = nonneg_number_set # non-negative
                elif Less(_a, _b).readily_provable():
                    restriction = neg_number_set # negative
                elif LessEq(_a, _b).readily_provable():
                    restriction = nonpos_number_set # non-positive
                elif NotEquals(_a, _b).readily_provable():
                    restriction = nonzero_number_set # non-zero
        
        # Use the positive, negative, non-negative, non-positive, or
        # non-zero restriction.
        if restriction is not None:
            return restriction[number_set]

        return number_set

    # IS THIS NECESSARY?
    @prover
    def deduce_difference_in_natural(self, **defaults_config):
        from proveit.numbers import Neg
        from proveit.numbers.number_sets.integers import difference_is_nat
        if not self.terms.is_double():
            raise ValueError("deduce_difference_in_natural only applicable "
                             "when there are two terms, got %s" % self)
        if not isinstance(self.terms[1], Neg):
            raise ValueError("deduce_difference_in_natural only applicable "
                             "for a subtraction, got %s" % self)
        thm = difference_is_nat
        return thm.instantiate({a: self.terms[0], b: self.terms[1].operand})

    # IS THIS NECESSARY?
    @prover
    def deduce_difference_in_natural_pos(self, **defaults_config):
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

    def readily_factorable(self, factor):
        '''
        Return True iff 'factor' is factorable from 'self' in an
        obvious manner.  For this Add, it is readily factorable if
        it is readily factorable from all terms.
        '''
        from proveit.numbers import readily_factorable
        if self == factor:
            return True
        for term in self.terms:
            if not readily_factorable(term, factor):
                return False
        return True

    @auto_equality_prover('factorized', 'factor')
    def factorization(self, the_factors, pull="left", 
                      group_factors=True, group_remainder=True,
                      **defaults_config):
        '''
        Factor out the factor(s) from this sum, pulling it either to 
        the "left" or "right".
        If group_factors is True, the factors are grouped
        together as a sub-product.
        In the Add case, the remainder will always be grouped (we
        have 'group_remainder' as a parameter just for recursion
        compatibility).
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
            if term == the_factors:
                if pull == 'left':
                    replacements.append(Mult(term, one).one_elimination(1))
                else:
                    replacements.append(Mult(one, term).one_elimination(0))
                _b.append(one)
            else:
                if not hasattr(term, 'factorization'):
                    raise ValueError(
                        "Factor, %s, is not present in the term at "
                        "index %d of %s!" %
                        (the_factors, _i, self))
                term_factorization = term.factorization(
                    the_factors, pull, group_factors=group_factors,
                    group_remainder=True)
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
                    expr.inner_expr().terms[_i]))
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
        _b = ExprTuple(*_b)
        _i = _a.num_elements()
        _j = _b.num_elements()
        _k = _c.num_elements()
        distribution = distribute_through_sum.instantiate(
            {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c}, 
            preserve_expr=expr, replacements=replacements)
        eq.update(distribution.derive_reversed())
        return eq.relation
    
    @equality_prover('combined_terms', 'combine_terms')
    def combining_terms(self, **defaults_config):
        '''
        Combine terms, adding their literal, rational coeffiicents.
        Alias for `combining_operands`.
        '''
        from proveit.numbers import one
        from proveit.numbers.multiplication.mult import (
                coefficient_and_remainder)
        # Obtain the common term "remainder" (sans coefficient),
        # raising a ValueError if the terms are not all like terms.
        likeness_key_fn = lambda term : (
                coefficient_and_remainder(term)[1])
        key = common_likeness_key(self, likeness_key_fn=likeness_key_fn)
        if key != one:
            # Factor out the common part from the coefficients.
            return self.factorization(key, pull="right")

        # All of the operands are rational, literals.
        if defaults.auto_simplify:
            # Simplify if auto-simplification is on.
            return self.simplification()
        else:
            return Equals(self, self).conclude_via_reflexivity()

    @equality_prover('combined_operands', 'combine_operands')
    def combining_operands(self, **defaults_config):
        '''
        Combine terms, adding their literal, rational coeffiicents.
        Alias for `combining_terms`.
        '''
        return self.combining_terms() 

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
        return apply_commutation_thm(
            self, init_idx, final_idx, commutation,
            leftward_commutation, rightward_commutation)
    
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

    @equality_prover('moved', 'move')
    def permutation_move(self, init_idx=None, final_idx=None,
                         **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal 
        to a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, (a + b + ... + y + z) = (a + ... + y + b + z)
        via init_idx = 1 and final_idx = -2.
        '''
        return self.commutation(init_idx, final_idx)

    @equality_prover('permuted', 'permute')
    def permutation(self, new_order=None, cycles=None, **defaults_config):
        '''
        Deduce that this Add expression is equal to an Add in which
        the terms at indices 0, 1, …, n-1 have been reordered as
        specified EITHER by the new_order list OR by the cycles list
        parameter. For example,
            (a+b+c+d).permutation_general(new_order=[0, 2, 3, 1])
        and
            (a+b+c+d).permutation_general(cycles=[(1, 2, 3)])
        would both return ⊢ (a+b+c+d) = (a+c+d+b).
        '''
        return generic_permutation(self, new_order, cycles)

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
                if isinstance(term_entry, ExprRange):
                    in_number_set = And(ExprRange(
                            term_entry.parameter,
                            InSet(term_entry.body, number_set),
                            term_entry.true_start_index, 
                            term_entry.true_end_index))
                else:
                    in_number_set = InSet(term_entry, number_set)
                if not in_number_set.readily_provable():
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
    def deduce_not_equal(self, other, *, try_deduce_number_set=True,
                         **defaults_config):
        '''
        Attempt to prove that self is not equal to other.
        '''
        from proveit.numbers import zero, Neg
        if other == zero:
            if self.terms.is_double():
                if isinstance(self.terms[1], Neg):
                    from .subtraction import nonzero_difference_if_different
                    _a = self.terms[0]
                    _b = self.terms[1].operand
                    if NotEquals(_a, _b).readily_provable():
                        # If we know (or can readily prove) that
                        # _a != _b then we can prove _a - _b != 0.
                        return nonzero_difference_if_different.instantiate(
                                {a:_a, b:_b})
            if try_deduce_number_set:
                # Try deducing the number set.
                number_set = readily_provable_number_set(self)
                if ComplexNonZero.readily_includes(number_set):
                    deduce_number_set(self)
                    return NotEquals(self, zero).prove()
        if NotEquals(self, other).readily_provable():
            # Readily provable.
            return NotEquals(self, other).prove()
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
    from proveit.numbers import is_numeric_int, zero, Neg
    if isinstance(expr, Neg):
        expr = Add(expr) # wrap in an Add so we can do quick_simplified
    if isinstance(expr, Add):
        expr = expr.quick_simplified()
        if (isinstance(expr, Add) and is_numeric_int(expr.terms[-1])):
            shift = expr.terms[-1].as_int()
            if expr.terms.num_entries() == 1:
                return shift
            elif (expr.terms.num_entries() == 2 and 
                    not isinstance(expr.terms[0], ExprRange)):
                return expr.terms[0], shift
            else:
                return Add(*expr.terms[:-1].entries), shift
    if is_numeric_int(expr):
        return zero, expr.as_int()
    return expr, 0
