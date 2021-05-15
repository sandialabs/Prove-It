from proveit import (defaults, Literal, Operation, USE_DEFAULTS, ExprTuple,
                     Judgment, ProofFailure, InnerExpr, equivalence_prover,
                     SimplificationDirectives)
from proveit.logic import Equals, InSet
from proveit.numbers import num
from proveit.numbers.number_sets import (Integer, Natural, NaturalPos, Real,
                                         RealNonNeg, RealPos, Complex)
import proveit.numbers.numerals.decimals
from proveit.numbers.numerals.decimals import DIGITS
from proveit import a, b, c, d, e, i, j, k, m, n, w, x, y, z
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, group_commutation, pairwise_evaluation
from proveit import TransRelUpdater
from proveit.numbers import NumberOperation

class Mult(NumberOperation):
    # operator of the Mult operation.
    _operator_ = Literal(string_format='*',  latex_format=r'\cdot',
                         theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            ungroup = True)

    # Multiplying two numerals may import a theorem for the evaluation.
    # Track which ones we have encountered already.
    multiplied_numerals = set()

    def __init__(self, *operands, styles=None):
        r'''
        Multiply together any number of operands from first operand.
        '''
        NumberOperation.__init__(self, Mult._operator_, operands,
                                 styles=styles)
        self.factors = self.operands
        if self.factors.is_double() and all(
                factor in DIGITS for factor in self.factors):
            if self not in Mult.multiplied_numerals:
                try:
                    # for single digit addition, import the theorem that
                    # provides the evaluation
                    Mult.multiplied_numerals.add(self)
                    proveit.numbers.numerals.decimals.__getattr__(
                        'mult_%d_%d' % (self.factors[0].as_int(), self.factors[1].as_int()))
                except BaseException:
                    # may fail before the relevent _commons_ and _theorems_
                    # have been generated
                    pass  # and that's okay

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Attempt to prove that this product is in the given number_set.
        '''
        from . import (
            mult_int_closure,
            mult_int_closure_bin,
            mult_nat_closure,
            mult_nat_closure_bin,
            mult_nat_pos_closure,
            mult_nat_pos_closure_bin,
            mult_real_closure,
            mult_real_closure_bin,
            mult_real_pos_closure,
            mult_real_pos_closure_bin,
            mult_real_non_neg_closure,
            mult_real_non_neg_closure_bin,
            mult_complex_closure,
            mult_complex_closure_bin)
        if hasattr(self, 'number_set'):
            number_set = number_set.number_set
        bin = False
        if number_set == Integer:
            if self.operands.is_double():
                thm = mult_int_closure_bin
                bin = True
            else:
                thm = mult_int_closure
        elif number_set == Natural:
            if self.operands.is_double():
                thm = mult_nat_closure_bin
                bin = True
            else:
                thm = mult_nat_closure
        elif number_set == NaturalPos:
            if self.operands.is_double():
                thm = mult_nat_pos_closure_bin
                bin = True
            else:
                thm = mult_nat_pos_closure
        elif number_set == Real:
            if self.operands.is_double():
                thm = mult_real_closure_bin
                bin = True
            else:
                thm = mult_real_closure
        elif number_set == RealPos:
            if self.operands.is_double():
                thm = mult_real_pos_closure_bin
                bin = True
            else:
                thm = mult_real_pos_closure
        elif number_set == Complex:
            if self.operands.is_double():
                thm = mult_complex_closure_bin
                bin = True
            else:
                thm = mult_complex_closure
        elif number_set == RealNonNeg:
            if self.operands.is_double():
                thm = mult_real_non_neg_closure_bin
                bin = True
            else:
                thm = mult_real_non_neg_closure
        else:
            raise NotImplementedError(
                "'Mult.deduce_in_number_set()' not implemented for the "
                "%s set" % str(number_set))
        # print("thm", thm)
        # print("self in deduce in number set", self)
        # print("self.operands", self.operands)
        if bin:
            return thm.instantiate({a: self.operands[0], b: self.operands[1]},
                                   assumptions=assumptions)
        return thm.instantiate({n: self.operands.num_elements(assumptions),
                                a: self.operands},
                               assumptions=assumptions)

    def deduce_divided_by(self, divisor, assumptions=USE_DEFAULTS):
        '''
        Deduce that the product represented by Mult(a,b) is divisible
        by the mult_factor a or b. For example,
           Mult(a, b).deduce_divided_by(a)
        returns |- Divides(a, Mult(a,b)), that is |- a|ab, (assuming
        complex a≠0 and integer b).
        Later: possibly consider an Equals(divisor,self.lhs) case?
        '''
        if divisor == self.operands[0]:  # a|ab
            from proveit.numbers.divisibility import (
                left_factor_divisibility)
            _x, _y = left_factor_divisibility.instance_params
            return left_factor_divisibility.instantiate(
                {_x: self.operands[0], _y: self.operands[1]},
                assumptions=assumptions)

        elif divisor == self.operands[1]:  # a|ba
            from proveit.numbers.divisibility import (
                right_factor_divisibility)
            _x, _y = right_factor_divisibility.instance_params
            return right_factor_divisibility.instantiate(
                {_x: self.operands[0], _y: self.operands[1]},
                assumptions=assumptions)

        else:
            raise ValueError(
                "In Mult({0}, {1}).deduce_divided_by({2}), "
                "the supplied divisor {2} does not appear "
                "to be equal to either of the multiplicands "
                "{0} or {1}.".
                format(self.operands[0], self.operands[1], divisor))

    def not_equal(self, rhs, assumptions=USE_DEFAULTS):
        from . import mult_not_eq_zero
        from proveit.logic import NotEquals
        from proveit.numbers import zero
        if rhs == zero:
            _n = self.operands.num_elements(assumptions)
            _a = self.operands
            return mult_not_eq_zero.instantiate({n: _n, a: _a},
                                                assumptions=assumptions)
        return NotEquals(self, zero).conclude_as_folded(assumptions)

    @equivalence_prover('shallow_evaluated', 'shallow_evaluate')
    def shallow_evaluation(self, **defaults_config):
        '''
        Returns a proven evaluation equation for this Mult
        expression assuming the operands have been simplified or
        raises an EvaluationError or ProofFailure (e.g., if appropriate
        number set membership has not been proven).
        
        Handle the trivial case of a zero factor or do pairwise
        evaluation after simplifying negations and eliminating one 
        factors.
        '''
        from . import mult_zero_left, mult_zero_right, mult_zero_any
        from proveit.logic import is_irreducible_value, EvaluationError
        from proveit.numbers import zero
        from . import empty_mult, unary_mult_reduction

        if self.operands.num_entries() == 0:
             # Multiplication with no operands is equal to 1.
            return empty_mult
                
        # First check for any zero factors 
        # -- quickest way to do an evaluation.
        try:
            zero_idx = self.operands.index(zero)
            if self.operands.is_double():
                if zero_idx == 0:
                    return mult_zero_left.instantiate({x: self.operands[1]})
                else:
                    return mult_zero_right.instantiate({x: self.operands[0]})
            _a = self.operands[:zero_idx]
            _b = self.operands[zero_idx + 1:]
            _i = _a.num_elements()
            _j = _b.num_elements()
            return mult_zero_any.instantiate({i: _i, j: _j, a: _a, b: _b})
        except (ValueError, ProofFailure):
            pass  # No such "luck" regarding a simple multiplication by zero.

        if not self.operands_are_irreducible():
            # Without a zero factor, shallow evaluation of Mult is only
            # viable if the operands are all irreducible.
            raise EvaluationError(self)
        
        if self.operands.is_single():
             # Multiplication with 1 operand is just that operand
            return unary_mult_reduction.instantiate({a:self.operands[0]})        

        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self)

        # Simplify negations -- factor them out.
        expr = eq.update(expr.neg_simplifications())

        if not isinstance(expr, Mult):
            # The expression may have changed to a negation after doing
            # neg_simplification.  Start the simplification of this new
            # expression fresh at this point.
            eq.update(expr.evaluation())
            return eq.relation

        # Eliminate any factors of one.
        expr = eq.update(expr.one_eliminations())

        if is_irreducible_value(expr):
            return eq.relation  # done

        if isinstance(expr, Mult) and expr.operands.num_entries() > 2:
            eq.update(pairwise_evaluation(expr))
            return eq.relation

        raise EvaluationError(self)

    @equivalence_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, **defaults_config):
        '''
        Returns a proven simplification equation for this Mult
        expression assuming the operands have been simplified.
        
        Deals with disassociating any nested multiplications,
        simplifying negations, and factors of one, in that order.
        Factors of 0 are dealt with in shallow_evaluation.
        '''
        from . import unary_mult_reduction
        
        if self.operands.is_single():
             # Multiplication with 1 operand is just that operand
            return unary_mult_reduction.instantiate({a:self.operands[0]})     

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(self)

        # Ungroup the expression (disassociate nested multiplications).
        if Mult._simplification_directives_.ungroup:
            idx = 0
            length = expr.operands.num_entries() - 1
            while idx < length:
                # loop through all operands
                if isinstance(expr.operands[idx], Mult):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(idx))
                else:
                    idx += 1
                length = expr.operands.num_entries()

        # Simplify negations -- factor them out.
        expr = eq.update(expr.neg_simplifications())

        if not isinstance(expr, Mult):
            # The expression may have changed to a negation after doing
            # neg_simplification.  Start the simplification of this new
            # expression fresh at this point.
            eq.update(expr.simplification())
            return eq.relation

        # Peform any cancelations between numerators and
        # denominators of different factors.  This will also
        # eliminate factors of one.
        expr = eq.update(expr.cancelations())

        return eq.relation

    def neg_simplifications(self, assumptions=USE_DEFAULTS):
        '''
        Equivalence method that derives a simplification in which
        negated factors are factored out.  For example:
            (-w)*(-x)*y*(-z) = -(w*x*y*z)
        '''
        from proveit.numbers import Neg

        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands.entries)):
            if isinstance(operand, Neg):
                idx = self.operands.num_entries() - rev_idx - 1
                if isinstance(expr, Mult):
                    expr = eq.update(expr.neg_simplification(idx, assumptions))
                elif isinstance(expr, Neg):
                    expr = eq.update(
                        expr.inner_neg_mult_simplification(
                            idx, assumptions))

        return eq.relation

    def neg_simplification(self, idx, assumptions=USE_DEFAULTS):
        '''
        Equivalence method that derives a simplification in which
        a specific negated factor, at the given index, is factored out.
        For example:
            w*(-x)*y*z = -(w*x*y*z)
        '''
        from proveit.numbers import Neg
        from . import mult_neg_left, mult_neg_right, mult_neg_any

        if not isinstance(self.operands[idx], Neg):
            raise ValueError(
                "Operand at the index %d expected to be a negation for %s" %
                (idx, str(self)))

        if self.operands.is_double():
            if idx == 0:
                _x = self.operands[0].operand
                _y = self.operands[1]
                return mult_neg_left.instantiate({x: _x, y: _y},
                                                 assumptions=assumptions)
            else:
                _x = self.operands[0]
                _y = self.operands[1].operand
                return mult_neg_right.instantiate({x: _x, y: _y},
                                                  assumptions=assumptions)
        _a = self.operands[:idx]
        _b = self.operands[idx].operand
        _c = self.operands[idx + 1:]
        _i = _a.num_elements(assumptions)
        _j = _c.num_elements(assumptions)
        return mult_neg_any.instantiate({i: _i, j: _j, a: _a, b: _b, c: _c},
                                        assumptions=assumptions)

    @equivalence_prover('eliminated_ones', 'eliminate_ones')
    def one_eliminations(self, **defaults_config):
        '''
        Equivalence method that derives a simplification in which
        factors of one are eliminated.  For example:
            x*1*y*1*z*1 = x*y*z
        '''
        from proveit.numbers import one

        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self)

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands.entries)):
            if operand == one:
                idx = self.operands.num_entries() - rev_idx - 1
                expr = eq.update(expr.one_elimination(idx))
                if not isinstance(expr, Mult):
                    # can't do an elimination if reduced to a single term.
                    break

        return eq.relation

    @equivalence_prover('eliminated_one', 'eliminate_one')
    def one_elimination(self, idx, **defaults_config):
        '''
        Equivalence method that derives a simplification in which
        a single factor of one, at the given index, is eliminated.
        For example:
            x*y*1*z = x*y*z
        '''
        from proveit.numbers import one
        from . import elim_one_left, elim_one_right, elim_one_any

        if self.operands[idx] != one:
            raise ValueError(
                "Operand at the index %d expected to be 1 for %s" %
                (idx, str(self)))

        if self.operands.is_double():
            if idx == 0:
                return elim_one_left.instantiate({x: self.operands[1]})
            else:
                return elim_one_right.instantiate({x: self.operands[0]})
        _a = self.operands[:idx]
        _b = self.operands[idx + 1:]
        _i = _a.num_elements()
        _j = _b.num_elements()
        return elim_one_any.instantiate({i: _i, j: _j, a: _a, b: _b})

    @equivalence_prover('deep_eliminated_ones', 'deep_eliminate_ones')
    def deep_one_eliminations(self, **defaults_config):
        '''
        Eliminate ones from direct factors as well as grouped
        factors and in fraction factors.
        '''
        expr = self

        # A convenience to allow successive update to the equation
        # via transitivities (starting with self=self).
        eq = TransRelUpdater(self)

        for _i, factor in enumerate(self.factors.entries):
            if hasattr(factor, 'deep_one_eliminations'):
                expr = eq.update(expr.inner_expr().factors[_i].
                                 deep_one_eliminations())

        expr = eq.update(expr.one_eliminations())
        return eq.relation

    @equivalence_prover('all_canceled', 'all_cancel')
    def cancelations(self, **defaults_config):
        '''
        Deduce and return an equality between self and a form in which
        all simple division cancellations are performed across the
        factors of this multiplication.
        '''
        from proveit.numbers import Div
        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self)

        # Eliminate any ones "deeply".  Ones can be eliminated without
        # any cancelation.
        expr = eq.update(self.deep_one_eliminations())

        numer_factors = []
        denom_factors = []
        for _i, factor in enumerate(self.factors.entries):
            if isinstance(factor, Div):
                if isinstance(factor.numerator, Mult):
                    numer_factors.extend(factor.numerator.factors)
                else:
                    numer_factors.append(factor.numerator)
                if isinstance(factor, Div):
                    if isinstance(factor.denominator, Mult):
                        denom_factors.extend(factor.denominator.factors)
                    else:
                        denom_factors.append(factor.denominator)
            elif isinstance(factor, Mult):
                numer_factors.extend(factor.factors)
            else:
                numer_factors.append(factor)
        denom_factors_set = set(denom_factors)

        for numer_factor in numer_factors:
            if numer_factor in denom_factors_set:
                expr = eq.update(expr.cancelation(numer_factor))
                denom_factors_set.remove(numer_factor)

        return eq.relation

    def cancelation(self, term_to_cancel, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        the given factor has been canceled in a numerator (or factor)
        and denominator.  For example,
        [a*b*c*(1/b)].cancelation(b) would return
        a*b*c*(1/b) = a*c
        '''
        from proveit.numbers import Div, zero, one
        expr = self
        eq = TransRelUpdater(expr, assumptions)

        if term_to_cancel in (zero, one):
            raise ValueError("'term_to_cancel' must not be zero or one")

        numer_occurrence_indices = []
        denom_occurrence_indices = []

        for _i, factor in enumerate(self.factors.entries):
            if isinstance(factor, Div):
                numer_factors = (factor.numerator.factors if
                                 isinstance(factor.numerator, Mult)
                                 else [factor.numerator])
                denom_factors = (factor.denominator.factors if
                                 isinstance(factor.denominator, Mult)
                                 else [factor.denominator])
            else:
                numer_factors = (factor.factors if
                                 isinstance(factor, Mult) else [factor])
                denom_factors = []
            if term_to_cancel in numer_factors:
                numer_occurrence_indices.append(_i)
            if term_to_cancel in denom_factors:
                denom_occurrence_indices.append(_i)

        if (len(numer_occurrence_indices) == 0 or
                len(denom_occurrence_indices) == 0):
            raise ValueError("No occurrences of %s to cancel were found "
                             "in %s" % (term_to_cancel, self))

        # If there is an occurrence of the numerator and denominator
        # within the same Div factor, that's ideal.
        intersection_indices = set(numer_occurrence_indices).intersection(
            set(denom_occurrence_indices))
        if len(intersection_indices) > 0:
            idx = sorted(intersection_indices)[0]
            eq.update(expr.inner_expr().factors[idx].cancellation(
                term_to_cancel, assumptions=assumptions))
            return eq.relation

        # Handle the special case of two neighboring factors which
        # serves as the base case.
        if expr.factors.is_double():
            from proveit.numbers.division import (
                mult_frac_cancel_numer_left, mult_frac_cancel_denom_left)

            # First, let's eliminate any ones from the canceling
            # parts (and division by one).  We'll also do this
            # for the instantiated theorm to ensure there is a match.
            numer_idx = numer_occurrence_indices[0]
            denom_idx = denom_occurrence_indices[0]

            def updated_canceling_numer_inner_expr():
                inner_expr = expr.inner_expr().factors[numer_idx]
                if isinstance(inner_expr.cur_sub_expr(), Div):
                    inner_expr = inner_expr.numerator
                return inner_expr, inner_expr.cur_sub_expr()

            def updated_canceling_denom_inner_expr():
                inner_expr = expr.inner_expr().factors[denom_idx]
                assert isinstance(inner_expr.cur_sub_expr(), Div)
                inner_expr = inner_expr.denominator
                return inner_expr, inner_expr.cur_sub_expr()
            canceling_numer_inner_expr, canceling_numer_expr = \
                updated_canceling_numer_inner_expr()
            if isinstance(canceling_numer_expr, Mult):
                one_elims = canceling_numer_inner_expr.deep_one_eliminations(
                    assumptions)
                if one_elims.lhs != one_elims.rhs:
                    # Update canceling numerator with one eliminations.
                    expr = eq.update(one_elims)
                    canceling_numer_inner_expr, canceling_numer_expr = \
                        updated_canceling_numer_inner_expr()
            canceling_denom_inner_expr, canceling_denom_expr = \
                updated_canceling_denom_inner_expr()
            if isinstance(canceling_denom_expr, Mult):
                one_elims = canceling_denom_inner_expr.deep_one_eliminations(
                    assumptions)
                if one_elims.lhs != one_elims.rhs:
                    # Update canceling denominator with one elims.
                    expr = eq.update(one_elims)
                    canceling_denom_inner_expr, canceling_denom_expr = \
                        updated_canceling_denom_inner_expr()

            # Factor the canceling numerator and denominator as
            # appropriate.
            if canceling_numer_expr != term_to_cancel:
                assert isinstance(canceling_numer_expr, Mult)
                pull = 'right' if numer_idx == 0 else 'left'
                expr = eq.update(canceling_numer_inner_expr.factorization(
                    term_to_cancel, pull=pull, group_factor=True,
                    group_remainder=True, assumptions=assumptions))
                canceling_numer_inner_expr, canceling_numer_expr = \
                    updated_canceling_numer_inner_expr()
            if canceling_denom_expr != term_to_cancel:
                assert isinstance(canceling_denom_expr, Mult)
                pull = 'right' if denom_idx == 0 else 'left'
                expr = eq.update(canceling_denom_inner_expr.factorization(
                    term_to_cancel, pull=pull, group_factor=True,
                    group_remainder=True, assumptions=assumptions))
                canceling_numer_inner_expr, canceling_numer_expr = \
                    updated_canceling_numer_inner_expr()

            left_factor, right_factor = expr.factors

            if numer_idx == 0:
                # numerator on the left side:
                assert denom_idx == 1
                assert isinstance(expr.factors[denom_idx], Div)
                # [(a*b)/c]*[(d/(b*e))] = (a/c)*(d/e)
                _b = term_to_cancel
                if isinstance(left_factor, Div):
                    _c = left_factor.denominator
                else:
                    _c = one
                if canceling_numer_expr == term_to_cancel:
                    _a = one
                else:
                    assert (isinstance(canceling_numer_expr, Mult) and
                            canceling_numer_expr.factors.is_double())
                    _a = canceling_numer_expr.factors[0]
                assert isinstance(right_factor, Div)
                _d = right_factor.numerator
                if canceling_denom_expr == term_to_cancel:
                    _e = one
                else:
                    assert (isinstance(canceling_denom_expr, Mult) and
                            canceling_denom_expr.factors.is_double())
                    _e = canceling_denom_expr.factors[1]
                cancelation = mult_frac_cancel_numer_left.instantiate(
                    {a: _a, b: _b, c: _c, d: _d, e: _e},
                    assumptions=assumptions)
            else:
                # numerator on the right side
                assert numer_idx == 1 and denom_idx == 0
                assert isinstance(expr.factors[denom_idx], Div)
                # [a/(b*c)]*[((c*e)/d)] = (a/b)*(d/e)
                _c = term_to_cancel
                if isinstance(left_factor, Div):
                    _a = left_factor.numerator
                else:
                    _a = one
                if canceling_denom_expr == term_to_cancel:
                    _b = one
                else:
                    assert (isinstance(canceling_denom_expr, Mult) and
                            canceling_denom_expr.factors.is_double())
                    _b = canceling_denom_expr.factors[0]
                if isinstance(right_factor, Div):
                    _d = right_factor.denominator
                else:
                    _d = one
                if canceling_numer_expr == term_to_cancel:
                    _e = one
                else:
                    assert (isinstance(canceling_numer_expr, Mult) and
                            canceling_numer_expr.factors.is_double())
                    _e = canceling_numer_expr.factors[1]
                cancelation = mult_frac_cancel_denom_left.instantiate(
                    {a: _a, b: _b, c: _c, d: _d, e: _e},
                    assumptions=assumptions)
            # Eliminate ones in the cancelation; it should now
            # match with the expression where we have already
            # eliminated ones.
            cancelation = (
                cancelation.inner_expr().lhs.deep_eliminate_ones(assumptions))
            cancelation = (
                cancelation.inner_expr().rhs.deep_eliminate_ones(assumptions))
            eq.update(cancelation)
            return eq.relation

        # If there are neighboring occurrences, that is the next
        # best thing.
        denom_occurrence_indices_set = set(denom_occurrence_indices)
        for numer_idx in numer_occurrence_indices:
            if numer_idx - 1 in denom_occurrence_indices_set:
                left_idx = numer_idx - 1
            elif numer_idx + 1 in denom_occurrence_indices_set:
                left_idx = numer_idx
            else:
                continue
            # Found neighboring occurrences.  Group, cancel,
            # then ungroup (if necessary).
            expr = eq.update(expr.inner_expr().association(
                left_idx, 2, assumptions=assumptions))
            expr = eq.update(
                expr.inner_expr().factors[left_idx].cancellation(
                    term_to_cancel, assumptions=assumptions))
            if isinstance(expr.factors[left_idx], Mult):
                expr = eq.update(
                    expr.inner_expr().disassociation(left_idx,
                                                     assumptions=assumptions))
            return eq.relation

        # As the last resort, we simply move the first occurrences
        # next to each other, cancel, then move them back if needed.
        # (This specific approach is a little funny since it will end up
        # swapping sides when they move next to each other, but it
        # should work fine and makes the code more straightforward.)
        numer_idx = numer_occurrence_indices[0]
        denom_idx = denom_occurrence_indices[0]
        expr = eq.update(
            expr.inner_expr().commutation(
                denom_idx, numer_idx, assumptions=assumptions))
        expr = eq.update(expr.inner_expr().cancelation(
            term_to_cancel, assumptions=assumptions))
        if expr.factors.num_entries() < self.factors.num_entries():
            # It must have been a complete cancelation, so no
            # reason to move anything back.
            return eq.relation
        # We should put things back where they were to play nice.
        expr = eq.update(
            expr.inner_expr().commutation(
                numer_idx, denom_idx, assumptions=assumptions))
        return eq.relation

    def conversion_to_addition(self, assumptions=USE_DEFAULTS):
        '''
        From multiplication by an integer as the first factor,
        derive and return the equivalence of this multiplication
        to a repeated addition; for example, 3*c = c + c + c.
        '''
        from . import mult_def
        if hasattr(self.operands[0], 'as_int'):
            reps = self.operands[0].as_int()
        else:
            raise ValueError(
                "Cannot 'expand_as_addition' unless the first operand is a literal integer: %s" %
                str(self))

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(self, assumptions)
        # Group together the remaining factors if necessary:
        if self.operands.num_entries() > 2:
            expr = eq.update(
                expr.association(
                    1, self.operands.num_entries() - 1, assumptions))
        _x = self.operands[1]
        _n = num(reps)
        eq.update(mult_def.instantiate({n: _n, a: [_x] * reps, x: _x},
                                       assumptions=assumptions))
        return eq.relation

    def index(self, the_factor, also_return_num=False):
        '''
        Return the starting index of the_factor, which may be a single 
        operand, a list of consecutive operands, or a Mult expression 
        that represents the product of the list of consecutive operands.
        If also_return_num is True, return a tuple of the index and 
        number of operands for the_factor.
        '''
        if isinstance(the_factor, Mult):
            the_factor = the_factor.operands.entries
        if (hasattr(the_factor, '__getitem__') and 
                hasattr(the_factor, '__len__')):
            # multiple operands in the_factor
            first_factor = the_factor[0]
            num = len(the_factor)
            idx = -1
            try:
                while True:
                    idx = self.operands.index(first_factor, start=idx + 1)
                    if self.operands[idx:idx + num].entries == tuple(the_factor):
                        break  # found it all!
            except ValueError:
                raise ValueError("Factor is absent!")
        else:
            num = 1
            try:
                idx = self.operands.index(the_factor)
            except ValueError:
                raise ValueError("Factor is absent!")
        return (idx, num) if also_return_num else idx

    def pull(
            self,
            start_idx=None,
            end_idx=None,
            direction='left',
            assumptions=USE_DEFAULTS):
        '''
        Pull a subset of consecutive operands, self.operands[start_idx:end_idx],
        to one side or another. Returns the equality that equates self to
        this new version.  Give any assumptions necessary to prove that the
        operands are in the Complex numbers so that the commutation theorem is applicable.
        '''
        if direction == "left":  # pull the factor(s) to the left
            if start_idx == 0 or start_idx is None:
                return Equals(self, self).prove(
                    assumptions)  # no move necessary
            return self.group_commutation(
                None, start_idx, start_idx, end_idx, assumptions=assumptions)
        elif direction == "right":  # pull the factor(s) to the right
            if end_idx == self.operands.num_entries() or end_idx is None:
                return Equals(self, self).prove(
                    assumptions)  # no move necessary
            return self.group_commutation(
                start_idx, end_idx, end_idx, None, assumptions=assumptions)
        else:
            raise ValueError(
                "Invalid pull direction!  (Acceptable values are \"left\" and \"right\".)")

    @equivalence_prover('distributed', 'distribute')
    def distribution(self, idx=None, **defaults_config):
        r'''
        Distribute through the operand at the given index.
        Returns the equality that equates self to this new version.
        Examples:
            a (b + c + a) d = a b d + a c d + a a d
            a (b - c) d = a b d - a c d
            a \left(\sum_x f(x)\right c = \sum_x a f(x) c
        Give any assumptions necessary to prove that the operands are in
        the Complex numbers so that the associative and commutation 
        theorems are applicable.
        '''
        from . import (distribute_through_sum, distribute_through_subtract,
                       distribute_through_abs_sum)# , distribute_through_summation
        from proveit.numbers.division import prod_of_fracs  # , frac_in_prod
        from proveit.numbers import Add, Neg, Abs, Div, Sum
        if (idx is None and self.factors.is_double() and 
                all(isinstance(factor, Div) for factor in self.factors)):
            return prod_of_fracs.instantiate(
                {x: self.factors[0].numerator,
                 y: self.factors[1].numerator,
                 z: self.factors[0].denominator,
                 w: self.factors[1].denominator})
        operand = self.operands[idx]
        _a = self.operands[:idx]
        _c = self.operands[idx + 1:]
        _i = _a.num_elements()
        _k = _c.num_elements()
        if (isinstance(operand, Add) and operand.operands.is_double()
              and isinstance(operand.operands[0], Neg)):
            _j = _k
            _x = self.operands[idx].operands[0]
            _y = self.operands[idx].operands[1].operand
            return distribute_through_subtract.instantiate(
                {i: _i, j: _j, a: _a, x: _x, y: _y, c: _c})
        elif isinstance(operand, Add):
            _b = self.operands[idx].operands
            _j = _b.num_elements()
            return distribute_through_sum.instantiate(
                {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c})
        elif isinstance(operand, Abs) and isinstance(operand.operand, Add):
            # For example, 
            # x * |a + b + c| * y * z = |x*a*y*z + x*b*y*z + x*c*y*z|
            # if x, y, and z are non-negative.
            _b = self.operands[idx].operand.operands
            _j = _b.num_elements()
            equiv = distribute_through_abs_sum.instantiate(
                {i: _i, j: _j, k: _k, a: _a, b: _b, c: _c})
            # As a convenient "side-effect" of this derivation,
            # if we know that the original was positive,
            # so is the new one.
            if all(InSet(operand, RealPos).proven() for 
                   operand in self.operands):
                InSet(self, RealPos).prove()
            return equiv
        elif isinstance(operand, Div):
            raise NotImplementedError("Mult.distribution must be updated "
                                      "for Div case.")
            '''
            eqn = frac_in_prod.instantiate({w_multi:self.operands[:idx], x:self.operands[idx].operands[0], y:self.operands[idx].operands[1], z_multi:self.operands[idx+1:]}, assumptions=assumptions)
            try:
                # see if the numerator can simplify (e.g., with a one factor)
                numer_simplification = eqn.rhs.numerator.simplification(assumptions=assumptions)
                dummy_var = eqn.safe_dummy_var()
                return numer_simplification.sub_right_side_into(Equals(eqn.lhs, frac(dummy_var, eqn.rhs.denominator)), dummy_var)
            except:
                return eqn
            '''
        elif isinstance(operand, Sum):
            raise NotImplementedError("Mult.distribution must be updated "
                                      "for Sum case.")
            '''
            y_multi_sub = operand.indices
            Pop, Pop_sub = Function(P, operand.indices), operand.summand
            S_sub = operand.domain
            x_dummy, z_dummy = self.safe_dummy_vars(2)
            spec1 = distribute_through_summation.instantiate({Pop:Pop_sub, S:S_sub, y_multi:y_multi_sub,
                                                           x_multi:Etcetera(Multi_variable(x_dummy)), z_multi:Etcetera(Multi_variable(z_dummy))}, assumptions=assumptions)
            return spec1.derive_conclusion().instantiate({Etcetera(Multi_variable(x_dummy)):self.operands[:idx], \
                                                        Etcetera(Multi_variable(z_dummy)):self.operands[idx+1:]}, assumptions=assumptions)
            '''
        else:
            raise Exception(
                "Unsupported operand type to distribute over: " + str(operand.__class__))

    @equivalence_prover('factorized', 'factor')
    def factorization(self, the_factor_or_index, pull="left",
                      group_factor=True, group_remainder=False,
                      **defaults_config):
        '''
        Return the proven factorization (equality with the factored
        form) from pulling "the_factor" from this product to the "left"
        or "right".  If there are multiple occurrences, the first 
        occurrence is used.  If group_factor is True and the_factor is 
        a product, these operands are grouped together as a sub-product.
        If group_remainder is True and there are multiple remaining 
        operands (those not in "the_factor"), then these remaining
        '''
        expr = self
        eq = TransRelUpdater(expr)
        if the_factor_or_index == self:
            return eq.relation # self = self
        if isinstance(the_factor_or_index, int):
            idx, num = the_factor_or_index, 1
        else:
            the_factor = the_factor_or_index
            idx, num = self.index(the_factor, also_return_num=True)
        expr = eq.update(self.group_commutation(
            idx, 0 if pull == 'left' else -num, length=num))
        if group_factor and num > 1:
            # use 0:num type of convention like standard python
            if pull == 'left':  
                expr = eq.update(expr.association(0, num))
            elif pull == 'right':
                expr = eq.update(expr.association(-num, num))
        if group_remainder and self.operands.num_entries() - num > 1:
            # if the factor has been group, effectively there is just 1
            # factor operand now
            num_factor_operands = 1 if group_factor else num
            num_remainder_operands = self.operands.num_entries() - num_factor_operands
            if pull == 'left':
                expr = eq.update(expr.association(
                        num_factor_operands, num_remainder_operands))
            elif pull == 'right':
                expr = eq.update(expr.association(
                        0, num_remainder_operands))
        return eq.relation

    @equivalence_prover('combined_exponents', 'combine_exponents')
    def exponent_combination(self, start_idx=None, end_idx=None,
                             **defaults_config):
        '''
        Equates $a^b a^c$ to $a^{b+c}$, $a^b a^{-c}$ to $a^{b-c}$,
        $a^b a$ to $a^{b+1}, $a a^b$ to $a^{1+b}, or
        $a^c b^c$ to $(a b)^c$.
        '''
        from proveit import ExprRange, free_vars
        from proveit.logic import And
        from proveit.numbers.exponentiation import (
            product_of_posnat_powers, products_of_posnat_powers,
            product_of_pos_powers, products_of_pos_powers,
            product_of_real_powers, products_of_real_powers,
            product_of_complex_powers, products_of_complex_powers)
        # from proveit.numbers.exponentiation import (
        #        sum_in_exp, diff_in_exp, diff_frac_in_exp)
        from proveit.numbers.exponentiation import (
            add_one_right_in_exp, add_one_left_in_exp)
        from proveit.numbers import Exp
        if start_idx is not None or end_idx is not None:
            dummy_var = self.safe_dummy_var()
            grouped = self.group(start_idx, end_idx)
            inner_combination = (
                grouped.rhs.factors[start_idx].
                exponent_combination())
            combine_in_group = (
                inner_combination.
                substitution(Mult(*(self.factors[:start_idx]
                                    + (dummy_var,)
                                    + self.factors[end_idx:])), dummy_var))
            return grouped.apply_transitivity(combine_in_group)
        # if all(isinstance(factor, Sqrt) for factor in self.factors):
        #     # combine the square roots into one square root
        #     factor_bases = [factor.base for factor in self.factors]
        #     return prod_of_sqrts.instantiate({x_multi:factor_bases},
        #                                   assumptions=assumptions)
        # the following sqrt instantiation modified by wdc on 2/29/2020
        # based on the above-commented-out code (kept here temporarily
        # until we're sure this works ok)

        exp_operand_msg = (
            'Combine exponents only implemented for a product '
            'of two exponentiated operands (or a simple variant)')

        if not self.operands.is_double() or not isinstance(
                self.operands[0], Exp) or not isinstance(
                self.operands[1], Exp):
            if (self.operands.is_double() and 
                    isinstance(self.operands[0], Exp) and 
                    self.operands[0].base == self.operands[1]):
                # Of the form a^b a
                return add_one_right_in_exp.instantiate(
                    {
                        a: self.operands[1],
                        b: self.operands[0].exponent},
                    ).derive_reversed()
            elif (self.operands.is_double() and 
                      isinstance(self.operands[1], Exp) and 
                      self.operands[1].base == self.operands[0]):
                # Of the form a a^b
                return add_one_left_in_exp.instantiate(
                    {
                        a: self.operands[0],
                        b: self.operands[1].exponent},
                    ).derive_reversed()
            raise NotImplementedError(
                "Need to better implement degenerate cases "
                "of a^b*a and a*a^b.")
            #raise ValueError(exp_operand_msg)

        # Create a list of bases and ranges of bases,
        # and a list of exponents and ranges of exponents,
        # and determine if all of the represented bases are the same
        # or if all of the represented exponents are the same.
        # For example,
        #   (a_1^c * ... * a_n^c * b^c)
        # would result in:
        #   same_base=False, same_exponent=c,
        #   operand_bases = [a_1, ..., a_n, b]
        #   operand_exonents = [c, ..n repeats.. c, c]
        operand_bases = []
        operand_exponents = []
        same_base = None
        same_exponent = None
        for operand in self.operands:
            if isinstance(operand, ExprRange):
                if not isinstance(operand.body, Exp):
                    raise ValueError(exp_operand_msg)
                operand_bases.append(operand.mapped_range(
                    lambda exponential: exponential.base))
                operand_exponents.append(operand.mapped_range(
                    lambda exponential: exponential.exponent))
                base = operand_bases.innermost_body()
                exponent = operand_exponents.innermost_body()
                operand_parameters = operand.parameters()
                if not free_vars(base, err_inclusively=True).isdisjoint(
                        operand_parameters):
                    # Can't have the same base unless the base
                    # is independent of range parameters.
                    same_base = False
                if not free_vars(exponent, err_inclusively=True).isdisjoint(
                        operand_parameters):
                    # Can't have the same exponent unless the exponent
                    # is independent of range parameters.
                    same_exponent = False
            else:
                if not isinstance(operand, Exp):
                    raise ValueError(exp_operand_msg)
                base = operand.base
                exponent = operand.exponent
                operand_bases.append(base)
                operand_exponents.append(exponent)
            if same_base is None:
                same_base = base
            elif same_base != base:
                # Not all bases are the same
                same_base = False
            if same_exponent is None:
                same_exponent = base
            elif same_exponent != base:
                # Not all exponents are the same
                same_exponent = False

        if same_base not in (None, False):
            # Same base: a^b a^c = a^{b+c}$, or something similar

            # Find out the known type of the exponents.
            possible_exponent_types = [NaturalPos, RealPos, Real,
                                       Complex]
            for exponent in operand_exponents:
                while len(possible_exponent_types) > 1:
                    exponent_type = possible_exponent_types[0]
                    if isinstance(exponent, ExprRange):
                        in_sets = exponent.mapped_range(
                            lambda exp_range_body:
                            InSet(exp_range_body, exponent_type))
                        if And(in_sets).proven():
                            # This type is known for these exponents.
                            break
                    else:
                        if InSet(exponent, exponent_type).proven():
                            # This type is known for this exponent.
                            break
                    # We've eliminated a type from being known.
                    possible_exponent_types.pop(0)
            known_exponent_type = possible_exponent_types[0]

            if known_exponent_type == NaturalPos:
                if self.base.operands.is_double():
                    _m, _n = operand_exponents
                    return product_of_posnat_powers.instantiate(
                        {a: same_base, m: _m, n: _n})
                else:
                    _k = ExprTuple(*operand_exponents)
                    _m = _k.num_elements()
                    return products_of_posnat_powers.instantiate(
                        {a: same_base, m: _m, k: _k})
            else:
                if self.operands.is_double():
                    _b, _c = operand_exponents
                    if known_exponent_type == RealPos:
                        thm = product_of_pos_powers
                    elif known_exponent_type == Real:
                        thm = product_of_real_powers
                    else:  # Complex is default
                        thm = product_of_complex_powers
                    return thm.instantiate({a: same_base, b: _b, c: _c})
                else:
                    _b = ExprTuple(*operand_exponents)
                    _m = _b.num_elements()
                    if known_exponent_type == RealPos:
                        thm = products_of_pos_powers  # plural products
                    elif known_exponent_type == Real:
                        thm = products_of_real_powers  # plural products
                    else:  # Complex is default
                        thm = products_of_complex_powers
                    return thm.instantiate({m: _m, a: same_base, b: _b})

        elif same_exponent not in (None, False):
            # Same exponent: equate $a^c b^c = (a b)^c$
            # Combining the exponents in this case is the reverse
            # of disibuting an exponent.
            prod = Mult(*operand_bases)
            exp = Exp(prod, same_exponent)
            return exp.distribution().derive_reversed()
        raise ValueError('Product is not in a correct form to '
                         'combine exponents: ' + str(self))

    @equivalence_prover('commuted', 'commute')
    def commutation(self, init_idx=None, final_idx=None, **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal
        to a form in which the operand at index init_idx has been moved
        to final_idx.
        For example, (a + b + ... + y + z) = (a + ... + y + b + z)
        via init_idx = 1 and final_idx = -2.
        '''
        from . import commutation, leftward_commutation, rightward_commutation
        return apply_commutation_thm(
            self, init_idx, final_idx, commutation,
            leftward_commutation, rightward_commutation)

    @equivalence_prover('group_commuted', 'group_commute')
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

    @equivalence_prover('associated', 'associate')
    def association(self, start_idx, length, **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal 
        to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (a * b * ... * y * z) = 
            (a * b ... * (l * ... * m) * ... * y * z)
        '''
        from . import association
        return apply_association_thm(
            self, start_idx, length, association)

    @equivalence_prover('disassociated', 'disassociate')
    def disassociation(self, idx, **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal 
        to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a * b ... * (l * ... * m) * ... * y* z)
            = (a * b * ... * y * z)
        '''
        from . import disassociation
        return apply_disassociation_thm(self, idx, disassociation)


    def bound_via_operand_bound(self, operand_relation, assumptions=USE_DEFAULTS):
        '''
        Alias for bound_via_factor_bound.
        Also see NumberOperation.deduce_bound.
        '''
        return self.bound_via_factor_bound(operand_relation, assumptions)

    def bound_via_factor_bound(self, factor_relation,
                               assumptions=USE_DEFAULTS):
        '''
        Deduce a bound of this multiplication via the bound on
        one of its factors.  For example
            a*b*c*d < a*z*c*d   given   b < z and a, c, d positive.

        Also see NumberOperation.deduce_bound.
        '''
        from proveit.numbers import (zero, NumberOrderingRelation,
                                     Less, greater, greater_eq)
        if isinstance(factor_relation, Judgment):
            factor_relation = factor_relation.expr
        if not isinstance(factor_relation, NumberOrderingRelation):
            raise TypeError("'factor_relation' expected to be a number "
                            "relation (<, >, ≤, or ≥)")
        idx = None
        for side in factor_relation.operands:
            try:
                idx, num = self.index(side, also_return_num=True)
                break
            except ValueError:
                pass
        if idx is None:
            raise TypeError("'factor_relation' expected to be a relation "
                            "for one of the factors; neither factor of %s "
                            "appears in the %s relation."
                            %(self, factor_relation))
        expr = self
        eq = TransRelUpdater(expr, assumptions)
        if num > 1:
            expr = eq.update(expr.association(idx, num,
                                              assumptions=assumptions))
        if expr.operands.is_double():
            # Handle the binary cases.
            assert 0 <= idx < 2
            if idx == 0:
                relation = factor_relation.right_mult_both_sides(
                        expr.factors[1], assumptions=assumptions)
            elif idx == 1:
                relation = factor_relation.left_mult_both_sides(
                        expr.factors[0], assumptions=assumptions)
            expr = eq.update(relation)
        else:
            thm = None
            if (isinstance(factor_relation, Less) and 
                    all(greater(factor, zero).proven(assumptions) for
                        factor in self.factors)):
                # We can use the strong bound.
                from . import strong_bound_via_factor_bound
                thm = strong_bound_via_factor_bound
            elif all(greater_eq(factor, zero).proven(assumptions) for
                     factor in self.factors):
                # We may only use the weak bound.
                from . import weak_bound_via_factor_bound
                thm = weak_bound_via_factor_bound
            if thm is not None:
                _a = self.factors[:idx]
                _b = self.factors[idx+1:]
                _i = _a.num_elements(assumptions)
                _j = _b.num_elements(assumptions)
                _x = factor_relation.normal_lhs
                _y = factor_relation.normal_rhs
                expr = eq.update(thm.instantiate(
                        {i: _i, j: _j, a: _a, b: _b, x: _x, y: _y},
                        assumptions=assumptions))
            else:
                # Not so simple.  Let's make it simpler by
                # factoring it into a binary multiplication.
                expr = eq.update(expr.factorization(
                        idx, pull='left', group_factor=True, 
                        group_remainder=True, assumptions=assumptions))
                expr = eq.update(expr.bound_via_factor_bound(
                        factor_relation, assumptions=assumptions))
                # Put things back as the were before the factorization.
                if isinstance(expr.factors[1], Mult):
                    expr = eq.update(expr.disassociation(1, assumptions))
                if idx != 0:
                    expr = eq.update(expr.commutation(0, idx, assumptions))
        if num > 1 and isinstance(expr.factors[idx], Mult):
            expr = eq.update(expr.disassociation(idx, assumptions))            
        relation = eq.relation
        if relation.lhs != self:
            relation = relation.with_direction_reversed()
        assert relation.lhs == self
        return relation
            
    def deduce_positive(self, assumptions=USE_DEFAULTS):
        # Deduce that this absolute value is greater than zero
        # given its argument is not equal zero.
        from proveit.numbers import RealPos, zero, greater
        InSet(self, RealPos).prove(assumptions)
        return greater(self, zero).prove(assumptions)
