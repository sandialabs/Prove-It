from collections import Counter
from proveit import (
        defaults, Expression, Literal, ExprTuple, ExprRange, 
        Judgment, ProofFailure, prover, relation_prover, equality_prover,
        SimplificationDirectives, TransRelUpdater, free_vars)
from proveit import a, b, c, d, e, i, j, k, m, n, w, x, y, z
from proveit.logic import (
    And, Equals, NotEquals, is_irreducible_value, EvaluationError, 
    InSet)
from proveit.numbers import (
    zero, one, num, Add, NumberOperation, deduce_number_set,
    standard_number_set, is_literal_int, is_literal_rational)
from proveit.numbers.number_sets import (
    Natural, NaturalPos,
    Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
    Rational, RationalNonZero, RationalPos, RationalNeg, RationalNonNeg,
    RationalNonPos,
    Real, RealNonZero, RealNeg, RealPos, RealNonNeg, RealNonPos,
    Complex, ComplexNonZero)
import proveit.numbers.numerals.decimals
from proveit.numbers.numerals.decimals import DIGITS
from proveit.abstract_algebra.generic_methods import (
        apply_commutation_thm, apply_association_thm, apply_disassociation_thm,
        group_commutation, pairwise_evaluation,
        deduce_equality_via_commutation, generic_permutation,
        sorting_and_combining_like_operands, sorting_operands)

class Mult(NumberOperation):
    # operator of the Mult operation.
    _operator_ = Literal(string_format='*',  latex_format=r'\cdot',
                         theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            ungroup=True, combine_exponents=True,
            # By default, sort such that literal, rationals come first 
            # and other irreducibles come next.
            order_key_fn = lambda factor : (
                    0 if is_literal_rational(factor) else (
                            1 if is_irreducible_value(factor) else 2)))

    def __init__(self, *operands, styles=None):
        r'''
        Multiply together any number of operands from first operand.
        '''
        NumberOperation.__init__(self, Mult._operator_, operands,
                                 styles=styles)
        self.factors = self.operands

    def _build_canonical_form(self):
        '''
        Returns a form of this Mult with operands in their canonical
        forms, nested multiplication is ungrouped, literal rational 
        factors are pulled to the front and turned into an irreducible 
        coefficient, "common" factors that are the same up to literal,
        rational exponents are combined, and these factors are
        deterministically sorted according to hash values of the
        exponential factor bases.  If, after pulling out the 
        'constants' and combining exponents, there is only one 
        non-constant factor that remains, and this factor is an Add 
        expression, distribute the constant through; that is,
            (2/3) * (a + b + c)  ->  (2/3)*a + (2/3)*b + (2/3)*c.
            
            [x * ((1/2)*y + ((2*z1)*(3*z2)*z3))] * 2
            
        Example:  (a/b)^{2/3) * c * (-2) * (a/b)^{-1/4} * c * (1/3) * d 
            ->    (-2/3) * a^{5/12} * b^{-5/12} * c^2  * d
        The order of the factors is arbitrary but deterministic
        (sorted by hash value) except the literal rational coefficient
        will be the first factor (or omitted if it is 1).
        '''
        from proveit.numbers import (Neg, Exp, one, 
                                     is_literal_rational,
                                     simplified_rational_expr)
        # Extract the literal rational factors from the rest.
        # Generate canonical forms of factors and ungroup nested
        # multiplications.
        def gen_factors():
            for factor in self.factors:
                canonical_factor = factor.canonical_form()
                if isinstance(canonical_factor, Mult):
                    for sub_factor in canonical_factor.factors:
                        yield sub_factor
                else:
                    yield canonical_factor
        # Populate base_to_exponent and extracted coefficient
        # numerator/denominator from the generated factors.
        numer, denom = 1, 1
        base_to_exponent = dict()
        for factor in gen_factors():
            if isinstance(factor, Neg):
                numer *= -1
                factor = factor.operand
            if is_literal_int(factor):
                numer *= factor.as_int()
            elif is_literal_rational(factor):
                numer *= factor.numerator.as_int()
                denom *= factor.denominator.as_int()
            else:
                if isinstance(factor, Exp) and (
                        is_literal_rational(factor.exponent)):
                    exponent = factor.exponent
                    base = factor.base
                else:
                    exponent = one
                    base = factor
                base = base.canonical_form() # canonize the base
                if base in base_to_exponent:
                    prev_exponent = base_to_exponent[base]
                    if isinstance(prev_exponent, Add):
                        exponent = Add(*prev_exponent.terms, exponent)
                    else:
                        exponent = Add(prev_exponent, exponent)
                base_to_exponent[base] = exponent
        if denom == 0:
            # Division by zero; the expression is garbage
            raise self # we can't do anything with it.
        coef = simplified_rational_expr(numer, denom)
        # Obtain the sorted, combined, canonical factors.
        factors = []
        for base in sorted(base_to_exponent.keys(), key=hash):
            # Canonize the exponentiated factor.
            factor = Exp(base, exponent).canonical_form()
            factors.append(factor)
        # Return the appropriate canonical form.
        if len(factors) == 0:
            return coef
        if coef == one:
            if len(factors) > 1:
                return Mult(*factors)
            else:
                return factors[0]
        if len(factors) == 1:
            # A single factor; if it is an Add, distribute the coef.
            factor = factors[0]
            if isinstance(factor, Add):
                return Add(*[Mult(coef, term).canonical_form() for term
                             in factor.terms])
        return Mult(coef, *factors)

    def _deduce_equality(self, equality):
        '''
        Prove that this Add is equal to an expression that has the
        same canonical form.
        '''
        lhs, rhs = equality.lhs, equality.rhs
        assert lhs == self
        assert lhs.canonical_form() == rhs.canonical_form()
        
        if isinstance(rhs, Add) and (
                Counter(lhs.terms.entries) == Counter(rhs.terms.entries)):
            # We just need to permute the entries.
            return deduce_equality_via_commutation(equality, one_side=self)
        
        # Since the canonical forms are the same, we should be
        # able to equate their simplifications via permutation.
        with Mult.temporary_simplification_directives() as simp_directives:
            # Make sure we use proper simplification directives.
            simp_directives.ungroup=True
            simp_directives.combine_exponents=True
            # don't bother reordering:
            simp_directives.order_key_fn=lambda term : 0
            lhs_simplification = lhs.simplification()
            rhs_simplification = rhs.simplification()
        eq_simps = Equals(lhs_simplification.rhs, 
                          rhs_simplification.rhs).prove()
        return Equals.apply_transitivities([lhs_simplification,
                                            eq_simps,
                                            rhs_simplification])

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Attempt to prove that this product is in the given number_set.
        '''
        import proveit.numbers.multiplication as mult_pkg
        if hasattr(self, 'number_set'):
            number_set = number_set.number_set
        bin = False
        if number_set == Integer:
            if self.operands.is_double():
                thm = mult_pkg.mult_int_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_int_closure
        elif number_set == Natural:
            if self.operands.is_double():
                thm = mult_pkg.mult_nat_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_nat_closure
        elif number_set == NaturalPos:
            if self.operands.is_double():
                thm = mult_pkg.mult_nat_pos_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_nat_pos_closure
        elif number_set == IntegerNonZero:
            if self.operands.is_double():
                thm = mult_pkg.mult_int_nonzero_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_int_nonzero_closure
        elif number_set == Rational:
            if self.operands.is_double():
                thm = mult_pkg.mult_rational_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_rational_closure
        elif number_set == RationalPos:
            if self.operands.is_double():
                thm = mult_pkg.mult_rational_pos_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_rational_pos_closure
        elif number_set == RationalNonNeg:
            if self.operands.is_double():
                thm = mult_pkg.mult_rational_nonneg_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_rational_nonneg_closure
        elif number_set == RationalNonZero:
            if self.operands.is_double():
                thm = mult_pkg.mult_rational_nonzero_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_rational_nonzero_closure
        elif number_set == Real:
            if self.operands.is_double():
                thm = mult_pkg.mult_real_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_real_closure
        elif number_set == RealPos:
            if self.operands.is_double():
                thm = mult_pkg.mult_real_pos_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_real_pos_closure
        elif number_set == RealNonNeg:
            if self.operands.is_double():
                thm = mult_pkg.mult_real_nonneg_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_real_nonneg_closure
        elif number_set == RealNonZero:
            if self.operands.is_double():
                thm = mult_pkg.mult_real_nonzero_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_real_nonzero_closure
        elif number_set == Complex:
            if self.operands.is_double():
                thm = mult_pkg.mult_complex_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_complex_closure
        elif number_set == ComplexNonZero:
            if self.operands.is_double():
                thm = mult_pkg.mult_complex_nonzero_closure_bin
                bin = True
            else:
                thm = mult_pkg.mult_complex_nonzero_closure
        else:
            raise NotImplementedError(
                "'Mult.deduce_in_number_set()' not implemented for the "
                "%s set" % str(number_set))
        if bin:
            return thm.instantiate({a: self.operands[0], b: self.operands[1]})
        return thm.instantiate({n: self.operands.num_elements(),
                                a: self.operands})

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most 
        restrictive standard number set we can readily know.
        '''
        from proveit.numbers import IntervalCC
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
        nonzero_sets = {NaturalPos, IntegerNeg, IntegerNonZero, 
                        RationalPos, RationalNeg, RationalNonZero,
                        RealPos, RealNeg, RealNonZero, ComplexNonZero}
        major_to_nonzero = {Natural: IntegerNonZero,
                            Rational: RationalNonZero,
                            Real: RealNonZero,
                            Complex: ComplexNonZero}

        major = minor = -1
        all_nonzero = True
        for factor in self.factors:
            factor_membership = deduce_number_set(factor)
            if isinstance(factor, ExprRange):
                # e.g. a_1 in S and ... and a_n in S
                factor_ns = factor_membership.operands[0].body.domain
            else:
                factor_ns = factor_membership.domain
            # check if factor_ns is not a standard number set
            if factor_ns not in number_set_map.keys():
                # try to replace factor_ns with a std number set
                factor_ns = standard_number_set(factor_ns)
            if factor_ns in number_set_map.keys():
                factor_ns = number_set_map[factor_ns]
            else:
                raise ValueError(
                        "In Mult.deduce_number_set(), the factor {0} "
                        "is not known to be in one of our standard "
                        "number sets (such as Real, RealPos, etc.), "
                        "and instead is just known to be in {1}.".
                        format(factor, factor_ns))
            if all_nonzero and factor_ns not in nonzero_sets:
                all_nonzero = False
            _major, _minor = priorities[factor_ns]
            major = max(_major, major)
            minor = max(_minor, minor)
        if major == minor == -1:
            major, minor = 3, 2 # Complex
        number_set = major_minor_to_set[(major, minor)]
        if all_nonzero and number_set in major_to_nonzero:
            number_set = major_to_nonzero # restrict to nonzero subset
        return self.deduce_in_number_set(number_set)

    @prover
    def deduce_divided_by(self, divisor, **defaults_config):
        '''
        Deduce that the product represented by Mult(a,b) is divisible
        by the divisor a or b. For example,
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
                preserve_expr=self)

        elif divisor == self.operands[1]:  # a|ba
            from proveit.numbers.divisibility import (
                right_factor_divisibility)
            _x, _y = right_factor_divisibility.instance_params
            return right_factor_divisibility.instantiate(
                {_x: self.operands[0], _y: self.operands[1]},
                preserve_expr=self)

        else:
            raise ValueError(
                "In Mult({0}, {1}).deduce_divided_by({2}), "
                "the supplied divisor {2} does not appear "
                "to be equal to either of the multiplicands "
                "{0} or {1}.".
                format(self.operands[0], self.operands[1], divisor))

    @relation_prover
    def not_equal(self, rhs, **defaults_config):
        from . import mult_not_eq_zero
        if rhs == zero:
            _n = self.operands.num_elements()
            _a = self.operands
            return mult_not_eq_zero.instantiate({n: _n, a: _a},
                                                auto_simplify=False)
        return NotEquals(self, rhs).conclude_as_folded()

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Mult
        expression assuming the operands have been simplified.

        Deals with disassociating any nested multiplications,
        simplifying negations, and factors of one, and factors of 0.
        '''
        from proveit.numbers import Exp, is_literal_rational
        from . import mult_zero_left, mult_zero_right, mult_zero_any
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
                    result = mult_zero_left.instantiate({x: self.operands[1]})
                    return result
                else:
                    return mult_zero_right.instantiate({x: self.operands[0]})
            _a = self.operands[:zero_idx]
            _b = self.operands[zero_idx + 1:]
            _i = _a.num_elements()
            _j = _b.num_elements()
            return mult_zero_any.instantiate({i: _i, j: _j, a: _a, b: _b})
        except (ValueError, ProofFailure):
            # No such "luck" regarding a simple multiplication by zero.
            pass

        if self.operands.is_single():
             # Multiplication with 1 operand is just that operand
            return unary_mult_reduction.instantiate(
                    {a:self.operands[0]}, auto_simplify=False)

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
                    expr = eq.update(expr.disassociation(
                            idx, preserve_all=True))
                else:
                    idx += 1
                length = expr.operands.num_entries()

        # Simplify negations -- factor them out.
        expr = eq.update(expr.neg_simplifications(auto_simplify=True))

        if not isinstance(expr, Mult):
            # The expression may have changed to a negation after doing
            # neg_simplification.  Start the simplification of this new
            # expression fresh at this point.
            eq.update(expr.shallow_simplification(
                    must_evaluate=must_evaluate))
            return eq.relation

        # Peform any cancelations between numerators and
        # denominators of different factors.  This will also
        # eliminate factors of one.
        # Since this is supposed to be a shallow simplification,
        # turn off auto-simplification for these cancelations.
        expr = eq.update(expr.cancelations(auto_simplify=False))

        if is_irreducible_value(expr):
            return eq.relation  # done

        if must_evaluate and not expr.operands_are_irreducible():
            # Without a zero factor, shallow evaluation of Mult is only
            # viable if the operands are all irreducible.
            for _k, factor in enumerate(expr.factors):
                if not is_irreducible_value(factor):
                    expr = eq.update(expr.inner_expr().operands[_k].evaluation(
                            preserve_all=True))
            # Start over now that the terms are all evaluated to
            # irreducible values.
            eq.update(expr.evaluation())
            return eq.relation
                    
            """
            
            
            # We should generalize this to work analogously like 
            # combining and sorting terms in Add.shallow_simplification,
            # but this at least handles the simple case of combining
            # exponents when all factors are exponents with the same 
            # base.
            # Only simple case of an ExprRange is currently handled.
            # We can improve this later as well.
            if (isinstance(expr, Mult) and expr.factors.num_entries()==1
                    and isinstance(expr.factors[0], ExprRange) and
                    expr.factors[0].is_parameter_independent):
                # x * x * ... * x = x^n
                factor_range = expr.factors[0]
                assert isinstance(factor_range, ExprRange)
                from proveit.numbers.exponentiation import exp_nat_pos_rev
                _x = factor_range.body                    
                _n = expr.operands.num_elements()
                if factor_range.start_index != one:
                    # Make the ExprRange start at 1.
                    eq.update(expr.inner_expr().operands[0].reduction())
                eq.update(exp_nat_pos_rev.instantiate(
                        {n:_n, x:_x}, preserve_expr=expr))
                return eq.relation
            if isinstance(expr, Mult) and expr.factors.num_entries()!=1:                 
                common_base = None
                has_exp_factor = False
                for factor in self.factors:
                    factor_base = None
                    if isinstance(factor, Exp):
                        has_exp_factor = True
                        factor_base = factor.base
                    else:
                        factor_base = factor
                    if common_base is None:
                        common_base = factor_base
                    elif common_base != factor_base:
                        common_base = None
                        break
                if has_exp_factor and (common_base is not None):
                    expr = eq.update(expr.exponent_combination())
            """
        
        if expr != self:
            if (must_evaluate or (
                    isinstance(expr, Mult) and 
                    not set(expr.factors.entries).issubset(
                            self.factors.entries))):
                # Try starting over with a call to
                # shallow_simplification, but only if must_evaluate
                # is True or we've done nothing but make some
                # cancelations -- that way, the simplification stays
                # shallow.
                eq.update(expr.shallow_simplification(
                        must_evaluate=must_evaluate))
            return eq.relation

        if all(is_literal_int(factor) for factor in self.factors):
            if self.operands.is_double():
                if all(factor in DIGITS for factor in self.factors):
                    # Prove single-digit multiplication by importing the
                    # appropriate theorem.
                    return proveit.numbers.numerals.decimals.__getattr__(
                        'mult_%d_%d' % (self.factors[0].as_int(), self.factors[1].as_int()))
                else:
                    raise NotImplementedError("Only single-digit multiplication "
                                              "is currently implemented")
            else:
                # Use pairwise evaluation when multiplying more then 2
                # operands.
                assert self.factors.num_entries() > 2
                return pairwise_evaluation(self)
        elif must_evaluate:
            raise NotImplementedError(
                "Cabability to evaluate %s is not implemented"%expr)

        order_key_fn = Mult._simplification_directives_.order_key_fn
        if Mult._simplification_directives_.combine_exponents and (
                not must_evaluate):
            # Like factors are ones whose canonical forms are
            # implicit/explicit exponentials with the same base
            # raised to a literal, rational power (everyting is
            # implicitly raised to the power of 1).
            def likeness_key_fn(factor):
                canonical_factor = factor.canonical_form()
                if isinstance(canonical_factor, Exp) and (
                        is_literal_rational(canonical_factor.exponenent)):
                    return canonical_factor.base
                else:
                    return canonical_factor
            # Sort and combine like operands.
            expr = eq.update(sorting_and_combining_like_operands(
                    expr, order_key_fn=order_key_fn, 
                    likeness_key_fn=likeness_key_fn,
                    preserve_likeness_keys=True, auto_simplify=True))
        else:
            # See if we should reorder the factors.
            expr = eq.update(sorting_operands(expr, order_key_fn=order_key_fn))        
        """
        if Mult._simplification_directives_.irreducibles_in_front:
            # Move irreducibles to the front.
            irreducible_factor_index_ranges = []
            _prev_was_irreducible = False
            _all_irreducible = True
            for _k, factor in enumerate(self.factors):
                if is_irreducible_value(factor):
                    if _prev_was_irreducible:
                        # Update a range of irreducible factors.
                        irreducible_factor_index_ranges[-1][-1] = _k
                    else:
                        # Start a new range of irreducibles.
                        irreducible_factor_index_ranges.append([_k, _k])
                    _prev_was_irreducible = True
                else:
                    _prev_was_irreducible = False
                    _all_irreducible = False
            if (len(irreducible_factor_index_ranges) > 0 and
                    not _all_irreducible):
                # Move one or more irreducible factors to the front.
                offset = 0
                for factor_index_range in reversed(
                        irreducible_factor_index_ranges):
                    # Move group of irreducibles to the front.
                    start, end = factor_index_range
                    expr = eq.update(expr.group_commutation(
                            start+offset, 0, end-start+1, 
                            auto_simplify=False))
                    offset += end - start + 1
        """
        
        return eq.relation # Should be self=self.

    @equality_prover('simplified_negations', 'simplify_negations')
    def neg_simplifications(self, **defaults_config):
        '''
        Equivalence method that derives a simplification in which
        negated factors are factored out.  For example:
            (-w)*(-x)*y*(-z) = -(w*x*y*z)
        '''
        from proveit.numbers import Neg

        expr = self

        # A convenience to allow successive update to the equation via
        # transitivities (starting with self=self).
        eq = TransRelUpdater(self)
        
        # Find out the first operand that is a negation for
        # the purpose of knowing when we should 'preserve all'.
        first_neg_operand_idx = None
        for idx, operand in enumerate(self.operands.entries):
            if isinstance(operand, Neg):
                first_neg_operand_idx = idx
                break
        if first_neg_operand_idx is None:
            return eq.relation # trivial self=self

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands.entries)):
            if isinstance(operand, Neg):
                idx = self.operands.num_entries() - rev_idx - 1
                # Preserve all until we process the final operand.
                preserve_all = (idx > first_neg_operand_idx)
                if isinstance(expr, Mult):
                    expr = eq.update(expr.neg_simplification(
                            idx, preserve_all=preserve_all))
                elif isinstance(expr, Neg):
                    expr = eq.update(
                        expr.inner_neg_mult_simplification(
                                idx, preserve_all=preserve_all))

        return eq.relation

    @equality_prover('simplified_negation', 'simplify_negation')
    def neg_simplification(self, idx, **defaults_config):
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
                return mult_neg_left.instantiate({x: _x, y: _y})
            else:
                _x = self.operands[0]
                _y = self.operands[1].operand
                return mult_neg_right.instantiate({x: _x, y: _y})
        _a = self.operands[:idx]
        _b = self.operands[idx].operand
        _c = self.operands[idx + 1:]
        _i = _a.num_elements()
        _j = _c.num_elements()
        return mult_neg_any.instantiate({i: _i, j: _j, a: _a, b: _b, c: _c})

    @equality_prover('eliminated_ones', 'eliminate_ones')
    def one_eliminations(self, **defaults_config):
        '''
        Equivalence method that derives a simplification in which
        factors of one are eliminated.  For example:
            x*1*y*1*z*1 = x*y*z
        '''
        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self)

        # Work in reverse order so indices don't need to be updated.
        for rev_idx, operand in enumerate(reversed(self.operands.entries)):
            if operand == one:
                idx = self.operands.num_entries() - rev_idx - 1
                expr = eq.update(expr.one_elimination(
                        idx, preserve_all=True))
                if not isinstance(expr, Mult):
                    # can't do an elimination if reduced to a single term.
                    break

        return eq.relation

    @equality_prover('eliminated_one', 'eliminate_one')
    def one_elimination(self, idx, **defaults_config):
        '''
        Equivalence method that derives a simplification in which
        a single factor of one, at the given index, is eliminated.
        For example:
            x*y*1*z = x*y*z
        '''
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

    @equality_prover('deep_eliminated_ones', 'deep_eliminate_ones')
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
                                 deep_one_eliminations(preserve_all=True))

        expr = eq.update(expr.one_eliminations(preserve_all=True))
        return eq.relation

    @equality_prover('all_canceled', 'all_cancel')
    def cancelations(self, **defaults_config):
        '''
        Deduce and return an equality between self and a form in which
        all simple division cancelations are performed across the
        factors of this multiplication.
        '''
        from proveit.numbers import Div
        expr = self

        # A convenience to allow successive update to the equation via
        # transitivities (starting with self=self).
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
                numer_factors.extend(factor.factors.entries)
            else:
                numer_factors.append(factor)
        denom_factors_set = set(denom_factors)

        for numer_factor in numer_factors:
            if numer_factor in denom_factors_set:
                expr = eq.update(expr.cancelation(numer_factor,
                                                  preserve_all=True))
                denom_factors_set.remove(numer_factor)

        return eq.relation

    @equality_prover('canceled', 'cancel')
    def cancelation(self, term_to_cancel, **defaults_config):
        '''
        Deduce and return an equality between self and a form in which
        the given factor has been canceled in a numerator (or factor)
        and denominator.  For example,
        [a*b*c*(1/b)].cancelation(b) would return
        a*b*c*(1/b) = a*c
        '''
        from proveit.numbers import Div, zero, one
        expr = self
        eq = TransRelUpdater(expr)

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
            eq.update(expr.inner_expr().factors[idx].cancelation(
                term_to_cancel))
            return eq.relation

        # Handle the special case of two neighboring factors which
        # serves as the base case.
        if expr.factors.is_double():
            from proveit.numbers.division import (
                mult_frac_cancel_numer_left, mult_frac_cancel_denom_left)

            # First, let's eliminate any ones from the canceling
            # parts (and division by one).  We'll also do this
            # for the instantiated theorem to ensure there is a match.
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
                one_elims = canceling_numer_inner_expr.deep_one_eliminations()
                if one_elims.lhs != one_elims.rhs:
                    # Update canceling numerator with one eliminations.
                    expr = eq.update(one_elims)
                    canceling_numer_inner_expr, canceling_numer_expr = \
                        updated_canceling_numer_inner_expr()
            canceling_denom_inner_expr, canceling_denom_expr = \
                updated_canceling_denom_inner_expr()
            if isinstance(canceling_denom_expr, Mult):
                one_elims = canceling_denom_inner_expr.deep_one_eliminations()
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
                    term_to_cancel, pull=pull, group_factors=True,
                    group_remainder=True))
                canceling_numer_inner_expr, canceling_numer_expr = \
                    updated_canceling_numer_inner_expr()
            if canceling_denom_expr != term_to_cancel:
                assert isinstance(canceling_denom_expr, Mult)
                pull = 'right' if denom_idx == 0 else 'left'
                expr = eq.update(canceling_denom_inner_expr.factorization(
                    term_to_cancel, pull=pull, group_factors=True,
                    group_remainder=True))
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
                    {a: _a, b: _b, c: _c, d: _d, e: _e})
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
                    {a: _a, b: _b, c: _c, d: _d, e: _e})
            # Eliminate ones in the cancelation; it should now
            # match with the expression where we have already
            # eliminated ones.
            cancelation = (
                cancelation.inner_expr().lhs.deep_eliminate_ones())
            cancelation = (
                cancelation.inner_expr().rhs.deep_eliminate_ones())
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
                left_idx, 2))
            expr = eq.update(
                expr.inner_expr().factors[left_idx].cancelation(
                    term_to_cancel))
            if isinstance(expr.factors[left_idx], Mult):
                expr = eq.update(
                    expr.inner_expr().disassociation(left_idx))
            return eq.relation

        # As the last resort, we simply move the first occurrences
        # next to each other, cancel, then move them back if needed.
        # (This specific approach is a little funny since it will end up
        # swapping sides when they move next to each other, but it
        # should work fine and makes the code more straightforward.)
        numer_idx = numer_occurrence_indices[0]
        denom_idx = denom_occurrence_indices[0]
        expr = eq.update(
            expr.inner_expr().commutation(denom_idx, numer_idx))
        expr = eq.update(expr.inner_expr().cancelation(term_to_cancel))
        if expr.factors.num_entries() < self.factors.num_entries():
            # It must have been a complete cancelation, so no
            # reason to move anything back.
            return eq.relation

        # If not already finished and returned, we should put things
        # back where they were to play nice.
        expr = eq.update(
            expr.inner_expr().commutation(numer_idx, denom_idx))
        return eq.relation

    @equality_prover('converted_to_addition', 'convert_to_addition')
    def conversion_to_addition(self, **defaults_config):
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
                "Cannot 'expand_as_addition' unless the first operand "
                "is a literal integer: %s" %str(self))

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(self)
        # Group together the remaining factors if necessary:
        if self.operands.num_entries() > 2:
            expr = eq.update(
                expr.association(
                    1, self.operands.num_entries() - 1,
                    preserve_expr=self.operands[0]))
        _x = self.operands[1]
        _n = num(reps)
        eq.update(mult_def.instantiate({n: _n, x: _x},
                                        auto_simplify=False))
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
                    if self.operands[idx:idx + num].entries == (
                            tuple(the_factor)):
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

    @equality_prover('distributed', 'distribute')
    def distribution(self, idx=None, **defaults_config):
        r'''
        Distribute through the operand at the given index.
        Returns the equality that equates self to this new version.
        Examples:
            a (b + c + a) d = a b d + a c d + a a d
            a (b - c) d = a b d - a c d
            a (\sum_x f(x)) c = \sum_x a f(x) c
            (a/b)*(c/d) = (a*b)/(c*d)
        Give any assumptions necessary to prove that the operands are in
        the Complex numbers so that the associative and commutation
        theorems are applicable.
        '''
        from . import (distribute_through_sum, distribute_through_subtract,
                       distribute_through_abs_sum)
        from proveit.numbers.division import prod_of_fracs
        from proveit.numbers import Neg, Abs, Div, Sum
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
              and isinstance(operand.operands[1], Neg)):
            _j = _k
            _x = self.operands[idx].operands[0]
            _y = self.operands[idx].operands[1].operand
            return distribute_through_subtract.instantiate(
                {i: _i, j: _j, a: _a, x: _x, y: _y, b: _c})
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
            return equiv
        elif isinstance(operand, Div):
            raise NotImplementedError("Mult.distribution must be updated "
                                      "for Div case.")
            '''
            eqn = frac_in_prod.instantiate(
                    {w_multi:self.operands[:idx],
                     x:self.operands[idx].operands[0],
                     y:self.operands[idx].operands[1],
                     z_multi:self.operands[idx+1:]}, assumptions=assumptions)
            try:
                # see if the numerator can simplify (e.g., with a one factor)
                numer_simplification = eqn.rhs.numerator.simplification(
                        assumptions=assumptions)
                dummy_var = eqn.safe_dummy_var()
                return numer_simplification.sub_right_side_into(
                        Equals(eqn.lhs, frac(dummy_var, eqn.rhs.denominator)),
                               dummy_var)
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
            spec1 = distribute_through_summation.instantiate(
                    {Pop:Pop_sub, S:S_sub, y_multi:y_multi_sub,
                     x_multi:Etcetera(Multi_variable(x_dummy)),
                     z_multi:Etcetera(Multi_variable(z_dummy))},
                     assumptions=assumptions)
            return spec1.derive_conclusion().instantiate(
                    {Etcetera(Multi_variable(x_dummy)):self.operands[:idx],
                     Etcetera(Multi_variable(z_dummy)):self.operands[idx+1:]},
                     assumptions=assumptions)
            '''
        else:
            raise Exception(
                "Unsupported operand type to distribute over: " +
                str(operand.__class__))

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factors_or_index, pull="left",
                      group_factors=True, group_remainder=False,
                      **defaults_config):
        '''
        Return the proven factorization (equality with the factored
        form) from pulling the factor(s) from this product to the 
        "left" or "right".  the_factors_or_index may be an iterable or 
        a Mult; in either case, the individual factors will be pulled
        together in the pull direction.
        If there are multiple occurrences, the first
        occurrence is used.  If group_factors is True, the factors are 
        grouped together as a sub-product.
        If group_remainder is True and there are multiple remaining
        operands, then these remaining
        '''
        expr = self
        eq = TransRelUpdater(expr)
        if the_factors_or_index == self:
            return eq.relation  # self = self

        if isinstance(the_factors_or_index, Expression):
            try:
                # Let's just see if the entire expression is a factor.
                the_factors_or_index = self.operands.entries.index(
                        the_factors_or_index)
            except ValueError:
                if isinstance(the_factors_or_index, Mult):
                    the_factors_or_index = (
                        the_factors_or_index.operands.entries)
                elif isinstance(the_factors_or_index, ExprTuple):
                    the_factors_or_index = the_factors_or_index.entries
                else:
                    the_factors_or_index = [the_factors_or_index]
        if isinstance(the_factors_or_index, int):
            idx = the_factors_or_index
            num = 1
            the_factor = self.operands[idx]
            expr = eq.update(expr.commutation(
                    idx, 0 if pull=='left' else -num,
                    preserve_expr=the_factor))    
            all_factors = [the_factor]
        else:
            # Look for one or more factors, pull them out,
            # grouping where possible.
            factors_iter = iter(the_factors_or_index)
            all_factors = []
            my_factors = self.operands.entries
            the_slice = None
            num = 0
            try:
                # Handle all but the last, always looking ahead one
                # to see if consecutive factors can move together.
                while True:
                    next_factor = next(factors_iter)
                    all_factors.append(next_factor)
                    try:
                        next_idx = my_factors.index(next_factor)
                    except ValueError:
                        raise ValueError(
                            "%s not found as a direct factor of %s"
                            %(next_factor, self))
                    if the_slice is None:
                        # We want to look ahead one if possible.
                        the_slice = slice(next_idx, next_idx+1)
                        continue
                    if next_idx == the_slice.stop:
                        # Extend the slice then look at the next one.
                        the_slice = slice(the_slice.start, next_idx+1)
                        continue
                    # Go ahead and move 'the_slice'
                    idx = the_slice.start
                    length = the_slice.stop - idx
                    # Preserve all until the last one.
                    expr = eq.update(expr.group_commutation(
                        idx, num if pull == 'left' else -num-length, 
                        length=length,
                        preserve_all=True))
                    num += length
                    the_slice = slice(next_idx, next_idx+1)
            except StopIteration:
                # Handle the last slice.
                preserved_exprs = (
                        defaults.preserved_exprs.union(all_factors))
                disassociate = (len(all_factors) > 1 or
                                not group_factors)
                idx = the_slice.start
                length = the_slice.stop - idx
                # Don't simplify if our goal is to group the factors
                # or remainder.  Simplification could defeat this 
                # purpose.
                preserve_all=(group_factors or group_remainder)
                expr = eq.update(expr.group_commutation(
                    idx, num if pull == 'left' else -num-length, 
                    length=length, disassociate=disassociate,
                    preserved_exprs=preserved_exprs,
                    preserve_all=preserve_all))
                num += length
        
        # Group the factors if needed.
        if group_factors and len(all_factors) > 1:
            # use 0:num type of convention like standard python
            if pull == 'left':
                expr = eq.update(expr.association(
                        0, num, preserve_all=True))
            elif pull == 'right':
                expr = eq.update(expr.association(
                        -num, num, preserve_all=True))
        num_factor_operands = 1 if group_factors else num
        if (group_remainder and 
                expr.operands.num_entries() - num_factor_operands > 1):
            # if the factor has been group, effectively there is just 1
            # factor operand now
            num_remainder_operands = (expr.operands.num_entries() -
                                      num_factor_operands)
            if pull == 'left':
                expr = eq.update(expr.association(
                        num_factor_operands, num_remainder_operands,
                        preserve_all=True))
            elif pull == 'right':
                expr = eq.update(expr.association(
                        0, num_remainder_operands, preserve_all=True))
        return eq.relation

    @equality_prover('combined_exponents', 'combine_exponents')
    def combining_exponents(self, start_idx=None, end_idx=None,
                             **defaults_config):
        '''
        Derive and return this Mult expression equated to the
        expression in which some or all of the exponential factors
        with common bases have been combined, or all or some of the
        exponential factors with common exponents have been combined.
        For example:
        |- a^b a^c    = a^{b+c},
        |- a^b a^{-c} = a^{b-c},
        |- a^b a      = a^{b+1},
        |- a a^b      = a^{1+b},
        |- a^c b^c    = (a b)^c. Maybe handle this case with something else?
        This also should work more generally with more than 2 factors,
        for example taking a^b a^c a^d to
        |- (a^b a^c a^d) = a^{b+c+d}.
        The start_idx and end_idx can be used to apply the process to
        a contiguous subset of factors within a larger set of factors.
        Automatically attempts to reduce a resulting new exponent sum,
        but not a new base product, unless call includes
        auto_simplify=False.
        Planned but not implemented: allow user to specify non-
        contiguous factors to combine. For example, given self as
        a^b a^c b^a a^d
        allow user to specify indices 0, 1, 3 to produce something like
        |- a^{b+c+d} b^a
        '''
        import proveit.numbers.exponentiation as exp_pkg
        from proveit.numbers import Exp

        error_msg = ""

        # If the start_idx and/or end_idx has been specified
        if start_idx is not None or end_idx is not None:

            # Compensate for potential missing indices in this block:
            # omission of either start or end idx defaults to a pair
            # of contiguous multiplicands
            if end_idx is None:
                end_idx = min(start_idx + 1, self.factors.num_entries())
            elif start_idx is None:
                start_idx = max(0, end_idx - 1)

            assoc_length = end_idx - start_idx + 1

            # associate the factors intended for combination
            # warning: 2nd arg of association() fxn is length not index
            grouped = self.association(start_idx, assoc_length,
                                       preserve_all=True)
            # isolate the targeted factors and combine them as desired
            # using call to this same method
            inner_combination = (
                    grouped.rhs.factors[start_idx].
                    exponent_combination())
            # substitute the combined factors back into the
            # grouped expression and return the deduced equality
            return inner_combination.sub_right_side_into(grouped)

        # Else neither the start_idx nor the end_idx has been specified,
        # indicating we intend to combine all possible factors, either:
        # (1) all like-bases combined with a single exponent, such as
        #     a^b a^c a^d = a^{b+c+d},
        # OR
        # (2) all like-exponents
        #     a^z b^z c^z = (abc)^z
        replacements = list(defaults.replacements)
        factors = []
        for factor in self.factors:
            if not isinstance(factor, Exp):
                # Exploit a^1 = a.
                factor = Exp(factor, one)
                replacements.append(factor.power_of_one_reduction())
            factors.append(factor)
        factor_bases = [factor.base for factor in factors]
        factor_exponents = [factor.exponent for factor in factors]
        from proveit.numbers.exponentiation import (
            products_of_complex_powers)

        # (1) all same bases to combine with a single exponent,
        # such as a^b a^c a^d = a^{b+c+d}
        if len(set(factor_bases)) == 1:

            _m_sub = num(len(factor_exponents))
            _a_sub = factor_bases[0]
            _b_sub = factor_exponents
            try:
                return products_of_complex_powers.instantiate(
                    {m: _m_sub, a: _a_sub, b: _b_sub},
                    replacements=replacements)
            except Exception as the_exception:
                # something went wrong
                error_msg = (
                    error_msg +
                    "All factors appeared to have same base, but "
                    "attempt failed with error message: \n" +
                    str(the_exception))
                pass

        # (2) all same exponent to combine with a single base,
        # such as a^d b^d c^d = (a b c)^d.
        # Less common but sometimes useful.
        if len(set(factor_exponents)) == 1:

            # Same exponent: equate $a^c b^c = (a b)^c$
            # Combining the exponents in this case is the reverse
            # of disibuting an exponent.
            _new_prod = Mult(*factor_bases)
            _new_exp = Exp(_new_prod, factor_exponents[0])
            try:
                return _new_exp.distribution(
                    replacements=replacements).derive_reversed()
            except Exception as the_exception:
                # something went wrong; append to error message
                error_msg = (
                    error_msg +
                    "All factors appeared to have the same exponent, "
                    "but attempt failed with error message: \n" +
                    str(the_exception)) + "\n"
                pass

        exp_operand_msg = (
            'Combine exponents only implemented for a product '
            'of two exponentiated operands (or a simple variant)')

        # I wonder if we might simply take any non-exp factor a and
        # convert it to Exp(a, one) (i.e. a^1). This might simplify
        # the process, making things a bit more mechanical ....

        if (not self.operands.is_double()
                or not isinstance(self.operands[0], Exp)
                or not isinstance(self.operands[1], Exp)):

            if (self.operands.is_double()
                    and isinstance(self.operands[0], Exp)
                    and self.operands[0].base == self.operands[1]):
                # self is of the form: (a^b) a
                return exp_pkg.add_one_right_in_exp.instantiate(
                    {a: self.operands[1], b: self.operands[0].exponent})

            elif (self.operands.is_double() and
                  isinstance(self.operands[1], Exp) and
                  self.operands[1].base == self.operands[0]):
                # self is of the form: a (a^b)

                try: # case where base a != 0
                    return exp_pkg.add_one_left_in_exp.instantiate(
                        {a: self.operands[0], b: self.operands[1].exponent})
                except Exception as the_exception:
                    # case where base might be 0 but exponent != 0
                    return (exp_pkg.add_one_left_in_exp_poss_zero_base
                            .instantiate({a: self.operands[0], 
                                          b: self.operands[1].exponent}))

        # More complex efforts if code above does not catch the
        # specific instance. The code below remains from earlier.
        # ============================================================
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
                if not free_vars(base).isdisjoint(operand_parameters):
                    # Can't have the same base unless the base
                    # is independent of range parameters.
                    same_base = False
                if not free_vars(exponent).isdisjoint(operand_parameters):
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
                deduce_number_set(exponent)
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
                if self.operands.is_double():
                    _m, _n = operand_exponents
                    return exp_pkg.product_of_posnat_powers.instantiate(
                        {a: same_base, m: _m, n: _n})
                else:
                    _k = ExprTuple(*operand_exponents)
                    _m = _k.num_elements()
                    return exp_pkg.products_of_posnat_powers.instantiate(
                        {a: same_base, m: _m, k: _k})
            else:
                if self.operands.is_double():
                    _b, _c = operand_exponents
                    if known_exponent_type == RealPos:
                        thm = exp_pkg.product_of_pos_powers
                    elif known_exponent_type == Real:
                        thm = exp_pkg.product_of_real_powers
                    else:  # Complex is default
                        thm = exp_pkg.product_of_complex_powers
                    return thm.instantiate({a: same_base, b: _b, c: _c})
                else:
                    _b = ExprTuple(*operand_exponents)
                    _m = _b.num_elements()
                    if known_exponent_type == RealPos:
                        thm = exp_pkg.products_of_pos_powers # plural
                    elif known_exponent_type == Real:
                        thm = exp_pkg.products_of_real_powers # plural
                    else:  # Complex is default
                        thm = exp_pkg.products_of_complex_powers
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

    @equality_prover('combined_operands', 'combine_operands')
    def combining_operands(self, **defaults_config):
        '''
        Combine factors, adding their literal, rational exponents.
        Alias for `exponent_combination`.
        '''
        return self.combining_exponents()    

    @equality_prover('common_power_extracted', 'common_power_extract')
    def common_power_extraction(self, start_idx=None, end_idx=None,
                                exp_factor=None,
                                **defaults_config):
        '''
        Derive and return this Mult expression equated to the
        expression in which some or all of the exponential factors
        in which a common factor occurs in the exponent, have been
        grouped and rewritten to be raised as a group to that common
        power.
        For example:
        |- a^c b^c    = (a b)^c
        |- a^{c d} b^{c k} = (a^{d} b^{k})^c
        This also should work more generally with more than 2 factors,
        for example taking a^k b^k c^k to
        |- (a^k b^k c^k) = (a b c)^k (Careful here … makes clear we need special cases!)
        The start_idx and end_idx can be used to apply the process to
        a contiguous subset of factors within a larger set of factors.
        Does NOT automatically attempt to reduce a resulting new
        product.
        Planned but not implemented: allow user to specify non-
        contiguous factors to combine. For example, given self as
        a^k b^c d^k e^d
        allow user to specify indices 0, 2 to produce something like
        |- a^k b^c d^k e^d = (a d)^k b^c e^d
        '''
        from proveit.numbers import Exp

        error_msg = ""

        # If the start_idx and/or end_idx has been specified
        if start_idx is not None or end_idx is not None:

            # Compensate for potential missing indices in this block:
            # omission of either start or end idx defaults to a pair
            # of contiguous multiplicands
            # ALSO should eventually check that the given indices
            # do NOT constitute the entire Mult expression; if we are
            # dealing with the entire expression, then the association
            # step should not be necessary (?)
            if end_idx is None:
                end_idx = min(start_idx + 1, self.factors.num_entries())
            elif start_idx is None:
                start_idx = max(0, end_idx - 1)

            assoc_length = end_idx - start_idx + 1

            # associate the factors intended for combination
            # warning: 2nd arg of association() fxn is length not index
            if (assoc_length == self.factors.num_elements().as_int()):
                # we have (inadvertently?) selected the entire expr,
                # so don't group factors; just call the same method
                # without specifying the indices
                return self.common_power_extraction(exp_factor=exp_factor)
            else:
                grouped = self.association(start_idx, assoc_length,
                                           preserve_all=True)
            # isolate the targeted factors and combine them as desired
            # using call to this same method
            inner_combination = (
                    grouped.rhs.factors[start_idx].
                    common_power_extraction(exp_factor=exp_factor))
            # substitute the combined factors back into the
            # grouped expression and return the deduced equality
            return inner_combination.sub_right_side_into(grouped)

        # Else neither the start_idx nor the end_idx has been specified,
        # indicating we intend to extract a common factor from all
        # the exponents of all exponential factors, like this:
        #     a^{i z} b^{j z} c^{k z} = (a^i b^j c^k)^z
        # for the moment assuming we have all exponential factors of
        # the form Exp(a, b) instead of something like a^b * a
        # NOTE: would be nice to generalize to deal with
        # exp_factor = None case, where we then search for and extract
        # ALL factors that all the exponents have in common.
        # For now, assume that exp_factor is NOT None.
        if exp_factor is None:
            raise NotImplementedError(
                    "'common_power_extraction()' not implemented for "
                    "cases in which kwarg exp_factor is not supplied.")
        if (all(isinstance(factor, Exp) for factor in self.factors)):
            # then we are dealing with factors that are ALL explicit
            # exponentials of the form a^k.
            factor_bases = [factor.base for factor in self.factors]
            factor_exponents = [factor.exponent for factor in self.factors]

            # (1) Simple case such as a^d b^d c^d, consisting of
            # exponential factors all of which have the same single
            # exponent. The more general case further below might
            # then re-call this sub-method after processing the factors.
            if len(set(factor_exponents)) == 1:
                # Same exponent: equate a^c b^c = (a b)^c
                # Combining the exponents in this case is the reverse
                # of distributing an exponent.
                _new_prod = Mult(*factor_bases)
                _new_exp = Exp(_new_prod, factor_exponents[0])
                try:
                    return _new_exp.distribution().derive_reversed()
                except Exception as the_exception:
                    raise Exception("An Exception! All factors appeared to "
                        "have the same exponent, but the Exp.distribution() "
                        "attempt failed with the following error message: "
                        "{}".format(the_exception))

            # (2) More complex case such as a^{fd} b^{dg} c^{dg},
            # consisting of exponential factors, the exponents of which
            # have the exp_factor as a factor somewhere. Strategy is
            # to factor out that exponent factor in each Mult factor,
            # then re-call the common_power_extraction() method on the
            # result, and Case (1) will then handle it.
            # This also handles the more general case of something like
            # a^d b^{dg}, where the exp_factor of 'd' might be a factor
            # in an exponent OR might be a stand-alone exponent
            temp_expr = self
            eq = TransRelUpdater(temp_expr)
            for idx in range(0, self.factors.num_elements().as_int()):
                if temp_expr.operands[idx].exponent != exp_factor:
                    temp_expr = eq.update(
                            temp_expr.inner_expr().operands[idx]
                            .exp_factorization(exp_factor, preserve_all=True))
            # eq.relation now has each factor with the specified the_factor
            # extracted to produce something along the lines of
            # |- a^{f j} b^{j, k} = (a^f)^j (b^k)^j
            # this now corresponds to case (1) above, so we should be able
            # to call this method again to handle that:
            eq.update(temp_expr.inner_expr().common_power_extraction(
                    exp_factor=exp_factor))
            return eq.relation
        
        raise ValueError(
                    "'Mult.common_power_extraction()' method works only "
                    "when all the specified multiplicands are instances "
                    "of Exp (i.e. each factor must be an exponential). "
                    "The method was instead called on the expression "
                    "{}".format(self))

    @equality_prover('commuted', 'commute')
    def commutation(self, init_idx=None, final_idx=None, **defaults_config):
        '''
        Given numerical operands, deduce that this expression is equal
        to a form in which the operand at index init_idx has been moved
        to final_idx.
        For example, (a · b · ... · y · z) = (a · ... · y · b · z)
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
        For example, (a · b · ... · y · z) = (a · ... · y · b · z)
        via init_idx = 1 and final_idx = -2.
        '''
        return self.commutation(init_idx=init_idx, final_idx=final_idx)

    @equality_prover('permuted', 'permute')
    def permutation(self, new_order=None, cycles=None, **defaults_config):
        '''
        Deduce that this Add expression is equal to an Add in which
        the terms at indices 0, 1, …, n-1 have been reordered as
        specified EITHER by the new_order list OR by the cycles list
        parameter. For example,
            (a·b·c·d).permutation_general(new_order=[0, 2, 3, 1])
        and
            (a·b·c·d).permutation_general(cycles=[(1, 2, 3)])
        would both return ⊢ (a·b·c·d) = (a·c·d·b).
        '''
        return generic_permutation(self, new_order, cycles)
    
    @equality_prover('associated', 'associate')
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

    @equality_prover('disassociated', 'disassociate')
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

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        Alias for bound_via_factor_bound.
        Also see NumberOperation.deduce_bound.
        '''
        return self.bound_via_factor_bound(operand_relation)

    @relation_prover
    def bound_via_factor_bound(self, factor_relation, **defaults_config):
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
                            % (self, factor_relation))
        expr = self
        eq = TransRelUpdater(expr)
        if num > 1:
            expr = eq.update(expr.association(idx, num))
        if expr.operands.is_double():
            # Handle the binary cases.
            assert 0 <= idx < 2
            if idx == 0:
                relation = factor_relation.right_mult_both_sides(
                        expr.factors[1])
            elif idx == 1:
                relation = factor_relation.left_mult_both_sides(
                        expr.factors[0])
            expr = eq.update(relation)
        else:
            thm = None
            for factor in self.factors:
                deduce_number_set(factor)
            if (isinstance(factor_relation, Less) and
                    all(greater(factor, zero).proven() for
                        factor in self.factors)):
                # We can use the strong bound.
                from . import strong_bound_via_factor_bound
                thm = strong_bound_via_factor_bound
            elif all(greater_eq(factor, zero).proven() for
                     factor in self.factors):
                # We may only use the weak bound.
                from . import weak_bound_via_factor_bound
                thm = weak_bound_via_factor_bound
            if thm is not None:
                _a = self.factors[:idx]
                _b = self.factors[idx+1:]
                _i = _a.num_elements()
                _j = _b.num_elements()
                _x = factor_relation.normal_lhs
                _y = factor_relation.normal_rhs
                expr = eq.update(thm.instantiate(
                        {i: _i, j: _j, a: _a, b: _b, x: _x, y: _y}))
            else:
                # Not so simple.  Let's make it simpler by
                # factoring it into a binary multiplication.
                expr = eq.update(expr.factorization(
                        idx, pull='left', group_factors=True,
                        group_remainder=True))
                expr = eq.update(expr.bound_via_factor_bound(factor_relation))
                # Put things back as the were before the factorization.
                if isinstance(expr.factors[1], Mult):
                    expr = eq.update(expr.disassociation(1))
                if idx != 0:
                    expr = eq.update(expr.commutation(0, idx))
        if num > 1 and isinstance(expr.factors[idx], Mult):
            expr = eq.update(expr.disassociation(idx))
        relation = eq.relation
        if relation.lhs != self:
            relation = relation.with_direction_reversed()
        assert relation.lhs == self
        return relation

    @relation_prover
    def deduce_positive(self, **defaults_config):
        '''
        Deduce that this product is greater than zero.
        '''
        from proveit.numbers import RealPos, zero, greater
        InSet(self, RealPos).prove()
        return greater(self, zero).prove()


def canonical_coefficient_and_remainder(expr):
    '''
    Returns the coefficient and remainder of the canonical form
    of the given expression.
    '''
    from proveit.numbers import is_literal_rational
    canonical_form = expr.canonical_form()
    if isinstance(canonical_form, Mult) and (
            is_literal_rational(canonical_form.factors[0])):
        coef = canonical_form.factors[0]
        num_factors = canonical_form.factors.num_entries()
        if num_factors > 2:
            remainder = Mult(*canonical_form.factors[1:])
        else:
            # A canonical Mult should have at least two factors:
            assert num_factors == 2
            remainder = canonical_form.factors[1]
    elif is_literal_rational(canonical_form):
        coef = canonical_form
        remainder = one
    else:
        coef = one
        remainder = canonical_form
    return coef, remainder