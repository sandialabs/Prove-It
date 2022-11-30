import math
from proveit import (Judgment, Expression, Literal, Operation,
                     maybe_fenced_latex, defaults,
                     Function, ExprTuple, InnerExpr, USE_DEFAULTS,
                     UnsatisfiedPrerequisites, relation_prover,
                     equality_prover, SimplificationDirectives)
from proveit import TransRelUpdater
from proveit import a, b, c, m, n, w, x, y, z
from proveit.logic import Equals, NotEquals, InSet
from proveit.numbers import (zero, NumberOperation, 
                             is_numeric_int, is_numeric_rational, 
                             numeric_rational_ints,
                             simplified_numeric_rational,
                             deduce_number_set, readily_provable_number_set)
from proveit.numbers.number_sets import (
    ZeroSet, Natural, NaturalPos,
    Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
    Rational, RationalNonZero, RationalPos, RationalNeg, RationalNonNeg,
    RationalNonPos,
    Real, RealNonZero, RealNeg, RealPos, RealNonNeg, RealNonPos,
    Complex, ComplexNonZero)

class Div(NumberOperation):
    # operator of the Div operation
    _operator_ = Literal(
        string_format='/',
        latex_format=r'\div',
        theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            factor_negation = True, 
            reduce_zero_numerator = True,
            reduce_to_multiplication = False,
            reduce_rational = True,
            distribute = False)

    def __init__(self, numerator, denominator, *, styles=None):
        r'''
        Divide two operands.
        '''
        NumberOperation.__init__(self, Div._operator_, [numerator, denominator],
                                 styles=styles)
        self.numerator = self.operands[0]
        self.denominator = self.operands[1]

    def latex(self, **kwargs):
        if self.get_style('division') == 'fraction':
            # only fence if force_fence=True (a fraction within an
            # exponentiation is an example of when fencing should be forced)
            kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
            return maybe_fenced_latex(
                r'\frac{' +
                self.numerator.latex() +
                '}{' +
                self.denominator.latex() +
                '}',
                **kwargs)
        else:
            # normal division
            return NumberOperation.latex(self, **kwargs)

    def style_options(self):
        '''
        Return the StyleOptions object for this Div.
        '''
        options = NumberOperation.style_options(self)
        options.add_option(
            name='division',
            description=("'inline': uses '/'; 'fraction': "
                         "numerator over the denominator "
                         "(also see 'frac' function)"),
            default='fraction',
            related_methods=('with_inline_style',
                             'with_fraction_style'))
        return options

    def with_inline_style(self):
        return self.with_styles(division='inline')

    def with_fraction_style(self):
        return self.with_styles(division='fraction')

    def remake_constructor(self):
        if self.get_style('division') == 'fraction':
            return 'frac'  # use a different constructor if using the fraction style
        return Operation.remake_constructor(self)

    def _build_canonical_form(self):
        '''
        If this is a literal rational, returns the irreducible form.
        Otherwise, returns the canonical form of the numerator
        multiplied by the denominator raised to the power of -1:
            x/y = x*y^{-1}
        '''
        from proveit.numbers import (one, Neg, Mult, Exp, 
                                     simplified_numeric_rational)
        if is_numeric_rational(self):
            # Return the irreducible rational.
            return simplified_numeric_rational(self.numerator.as_int(),
                                            self.denominator.as_int())
        as_mult = Mult(self.numerator, Exp(self.denominator, Neg(one)))
        return as_mult.canonical_form()

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Divide
        expression assuming the operands have been simplified.

        Specifically, cancels common factors and eliminates ones.
        '''
        from proveit.logic import is_irreducible_value
        from proveit.numbers import one, Neg, Add, Sum, Mult, num

        if self.is_irreducible_value():
            # already irreducible
            return Equals(self, self).conclude_via_reflexivity()
        
        numer, denom = self.numerator, self.denominator
        if Div._simplification_directives_.reduce_rational and (
                is_numeric_rational(numer) and is_numeric_rational(denom) 
                and denom != zero):
            # If the numerator and denominator are rational numerals, 
            # so go ahead and evaluate it to an irreducible form.
            return self.rational_reduction()
        
        if Div._simplification_directives_.reduce_to_multiplication:
            # (x/y) = x*y^{-1}_deduce
            return self.reduction_to_mult(auto_simplify=True)
        
        # for convenience updating our equation
        expr = self
        eq = TransRelUpdater(expr)

        # perform cancelations where possible
        expr = eq.update(expr.cancelations(preserve_all=True))
        if not isinstance(expr, Div):
            # complete cancelation.
            return eq.relation

        if must_evaluate:
            if not all(is_irreducible_value(operand) for operand 
                       in self.operands):
                for operand in self.operands:
                    if not is_irreducible_value(operand):
                        # The simplification of the operands may not have
                        # worked hard enough.  Let's work harder if we
                        # must evaluate.
                        operand.evaluation()
                return self.evaluation()
            canonical_form = self.canonical_form()
            if is_numeric_rational(canonical_form):
                return self.rational_reduction()
            elif is_irreducible_value(canonical_form):
                # Equate to the irreducible canonical form.
                return Equals(self, canonical_form).prove()
            raise NotImplementedError(
                    "Evaluation of %s is not implemented"%self)

        if expr.denominator == one:
            # eliminate division by one
            expr = eq.update(expr.divide_by_one_elimination(preserve_all=True))

        if (isinstance(expr, Div) and
              Div._simplification_directives_.factor_negation and
              isinstance(expr.numerator, Neg)):
            # we have something like (-a)/b but want -(a/b)
            expr = eq.update(expr.neg_extraction())
            # return eq.relation  # no more division simplifications.

        if (Div._simplification_directives_.reduce_zero_numerator and
            isinstance(expr, Div)):
            if ((expr.numerator==zero or Equals(expr.numerator, 
                                                zero).readily_provable())
                and NotEquals(expr.denominator, zero).readily_provable()):
                # we have something like 0/x so reduce to 0
                expr = eq.update(expr.zero_numerator_reduction())
        
        # finally, check if we have something like
        # (x/(y/z)) or ((x/y)/z)
        # but! remember to check here if we still even have a Div expr
        # b/c some of the work above might have changed it to
        # something else!
        if (isinstance(expr, Div) # (x/(y/z))
            and isinstance(expr.denominator, Div)
            and NotEquals(expr.denominator.numerator, zero).readily_provable()
            and NotEquals(expr.denominator.denominator, 
                          zero).readily_provable()):
            expr = eq.update(expr.div_in_denominator_reduction())
        if (isinstance(expr, Div) # (x/y)/z)
            and isinstance(expr.numerator, Div)
            and NotEquals(expr.numerator.denominator, zero).proven()
            and NotEquals(expr.denominator, zero).proven() ):
            expr = eq.update(expr.div_in_numerator_reduction())

        if Div._simplification_directives_.distribute and (
                isinstance(self.numerator, Add) or 
                isinstance(self.numerator, Sum)):
            expr = eq.update(expr.distribution())

        if Div._simplification_directives_.reduce_rational and (
                isinstance(expr, Div)):
            # Reduce numeric rationals in the numerator and denominator
            # to an irreducible rational form.
            expr = eq.update(expr.rational_reduction())

        return eq.relation

    def is_irreducible_value(self):
        '''
        This needs work, but we know that 1/x is irreducible if
        x is irreducible, not a negation, not 0 and not 1.
        '''
        if is_numeric_int(self.numerator) and is_numeric_int(self.denominator):
            # This is an irreducible rational if and only if it is the
            # same as the corresponding 'simiplified_rational_expr'.
            # (which divides out the gcd and extracts any negation).
            numer_int = self.numerator.as_int()
            denom_int = self.denominator.as_int()
            return self == simplified_numeric_rational(numer_int, denom_int)
        return False

    @equality_prover('rational_reduced', 
                     'reduce_rational')
    def rational_reduction(self, **defaults_config):
        '''
        Equate this fraction to an irreducible, numeric rational if
        it is a numeric rational.  More generally, reduce the numeric
        rationals in the numerator and denominator to an irreducible 
        rational form.  For example:
            ((4/3) x) / ((2/3) y) = (2 x) / y
        '''
        from proveit.numbers import Mult, num, one, compose_factors
        from proveit.numbers.division import frac_cancel_left

        numerator, denominator = self.numerator, self.denominator
        canonical_numer = self.numerator.canonical_form()
        canonical_denom = self.denominator.canonical_form()
        # Treat the case where the numerator and denominator evaluate
        # to integers.
        if is_numeric_int(canonical_numer) and is_numeric_int(canonical_denom):
            # Find out the greatest common divisor.
            numer, denom = canonical_numer, canonical_denom
            numer_int, denom_int = numer.as_int(), denom.as_int()
            if abs(numer_int) == abs(denom_int):
                if numer_int != denom_int:
                    # -n/n = -1 or n/(-n) = -1
                    return self.neg_extraction(auto_simplify=True)
                # n/n=1
                replacements = [Equals(numer, self.numerator).prove(),
                                Equals(denom, self.denominator).prove()]
                return Div(numer, denom).cancelation(
                        num(abs(numer_int)), replacements=replacements,
                        preserve_expr=self, alter_lhs=True)
            gcd = math.gcd(numer_int, denom_int)
            expr = self
            eq = TransRelUpdater(expr)
            if gcd == 1:
                # No common divisor to factor out.
                expr = eq.update(expr.inner_expr().numerator.evaluation())
                expr = eq.update(expr.inner_expr().denominator.evaluation())
            else:
                # Factor out the gcd and cancel it.
                # Replace the factored numerator and denominator with 
                # the original form.
                factored_numer = Mult(num(gcd), num(numer_int//gcd))
                factored_denom = Mult(num(gcd), num(denom_int//gcd))
                numer_eval = self.numerator.evaluation()
                denom_eval = self.denominator.evaluation()
                replacements = [
                        factored_numer.evaluation().apply_transitivity(
                                numer_eval),
                        factored_denom.evaluation().apply_transitivity(
                                denom_eval),
                        ]
                expr = eq.update(frac_cancel_left.instantiate(
                        {x: num(gcd), y: factored_numer.factors[1], 
                         z: factored_denom.factors[1]},
                        replacements=replacements, preserve_expr=self))
            if numer_int < 0 and denom_int < 0:
                # cancel negations in the numerator and denominator
                expr = eq.update(expr.neg_cancelation())
            elif numer_int < 0 or denom_int < 0:
                # extract the negation for the irreducible form.
                expr = eq.update(expr.neg_extraction())
            if abs(denom_int) == 1:
                expr = eq.update(expr.divide_by_one_elimination())
            return eq.relation

        canonical_form = self.canonical_form()
        if  is_numeric_rational(canonical_form):
            # Reduce to a multiplication and then sort it out to handle
            # the more general case.
            return self.reduction_to_mult(auto_simplify=True)
        
        # Extract the rational and remainder parts of the
        # numerator and denominator.
        numer_rational = denom_rational = one
        numer_remainder_factors = denom_remainder_factors = []
        if is_numeric_rational(numerator):
            numer_rational = numerator
        elif isinstance(numerator, Mult) and (
                len(numerator.operands) > 0 and
                is_numeric_rational(numerator.operands[0])):
            numer_rational = numerator.operands[0]
            numer_remainder_factors = numerator.operands[1:]
        elif numerator != one:
            numer_remainder_factors = [numerator]
        if is_numeric_rational(denominator):
            denom_rational = denominator
        elif isinstance(denominator, Mult) and (
                len(denominator.operands) > 0 and
                is_numeric_rational(denominator.operands[0])):
            denom_rational = denominator.operands[0]
            denom_remainder_factors = denominator.operands[1:]
        elif denominator != one:
            denom_remainder_factors = [denominator]
        numer_ints = numeric_rational_ints(numer_rational)
        denom_ints = numeric_rational_ints(denom_rational)
        # (a/b)/(c/d) = (a*d)/(b*c):
        numer_int = numer_ints[0] * denom_ints[1]
        denom_int = denom_ints[0] * numer_ints[1]
        numer_int, denom_int = numeric_rational_ints(
                simplified_numeric_rational(numer_int, denom_int))
        if numer_int != numer_rational or denom_int != denom_rational:
            # A simplification should be performed.
            if numer_int == 1:
                numer = compose_factors(*numer_remainder_factors)
            else:
                numer = compose_factors(num(numer_int), 
                                        *numer_remainder_factors)
            if denom_int == 1:
                denom = compose_factors(*denom_remainder_factors)
            else:
                denom = compose_factors(num(denom_int), 
                                        *denom_remainder_factors)
            if denom == one:
                rhs = numer
            else:
                rhs = Div(numer, denom)
            return self.deduce_canonically_equal(rhs)

        return Equals(self, self).conclude_via_reflexivity()
    
    @equality_prover('reduced_to_mult', 'reduce_to_mult')
    def reduction_to_mult(self, **defaults_config):
        '''
        Equate (x/y) to x*y^{-1}.
        '''
        from proveit.numbers.division import div_as_mult
        return div_as_mult.instantiate({x:self.numerator, 
                                        y:self.denominator})
        
    @equality_prover('zero_numerator_reduced', 'zero_numerator_reduce')
    def zero_numerator_reduction(self, **defaults_config):
        '''
        Deduce and return an equality between self of the form 0/x
        and the number 0. Will need to know or assume that the
        denominator x is non-zero.
        '''
        from proveit.numbers.division import frac_zero_numer
        _x_sub = self.denominator
        return frac_zero_numer.instantiate({x: _x_sub})

    @equality_prover('div_in_denominator_reduced', 'div_in_denominator_reduce')
    def div_in_denominator_reduction(self, **defaults_config):
        '''
        Deduce and return an equality between self of the form
        (x/(y/z)) (i.e. a fraction with a fraction as it denominator)
        and the form x (z/y). Will need to know or assume that x, y, z
        are Complex with y != 0 and z != 0.
        '''
        if (not isinstance(self.denominator, Div)):
            raise ValueError(
                    "Div.div_in_denominator_reduction() method only "
                    "applicable when the denominator is itself a Div."
                    "Instead we have the expr {0} with denominator {1}.".
                    format(self, self.denominator))
        from proveit.numbers.division import div_by_frac_is_mult_by_reciprocal
        return div_by_frac_is_mult_by_reciprocal.instantiate(
                {x: self.numerator, y: self.denominator.numerator,
                 z: self.denominator.denominator})

    @equality_prover('div_in_numerator_reduced', 'div_in_numerator_reduce')
    def div_in_numerator_reduction(self, **defaults_config):
        '''
        Deduce and return an equality between self of the form
        (x/y)/z (i.e. a fraction with a fraction as its numerator)
        and the form x/(yz). Will need to know or assume that x, y, z
        are Complex with y != 0 and z != 0.
        '''
        if (not isinstance(self.numerator, Div)):
            raise ValueError(
                    "Div.div_in_numerator_reduction() method only "
                    "applicable when the numerator is itself a Div."
                    "Instead we have the expr {0} with numerator {1}.".
                    format(self, self.numerator))
        from proveit.numbers.division import numerator_frac_reduction
        return numerator_frac_reduction.instantiate(
                {x: self.numerator.numerator, y: self.numerator.denominator,
                 z: self.denominator})


    @equality_prover('all_canceled', 'all_cancel')
    def cancelations(self, **defaults_config):
        '''
        Deduce and return an equality between self and a form in which
        all simple division cancelations are performed.
        '''
        from proveit.numbers import Neg, Mult
        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self)
        
        if isinstance(expr.numerator, Neg) and (
                isinstance(expr.denominator, Neg)):
            # cancel negation in the numerator and denominator.
            expr = eq.update(expr.neg_cancelation(preserve_all=True))

        numer_factors = (expr.numerator.operands if
                         isinstance(expr.numerator, Mult) else
                         [expr.numerator])
        denom_factors = (expr.denominator.operands if
                         isinstance(expr.denominator, Mult) else
                         [expr.denominator])
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
        the given operand has been canceled on the numerator and
        denominator.  For example,
        [(a*b)/(b*c)].cancelation(b) would return
        (a*b)/(b*c) = a / c.
        Assumptions or previous work might be required to establish
        that the term_to_cancel is non-zero.
        '''
        from proveit.numbers import one, Exp, Mult, Neg

        if self.numerator == self.denominator == term_to_cancel:
            # x/x = 1
            from . import frac_cancel_complete
            return frac_cancel_complete.instantiate(
                {x: term_to_cancel})

        expr = self
        eq = TransRelUpdater(expr)
        if term_to_cancel != self.numerator:
            # try to catch Exp objects here as well?
            # after all, Exp(term_to_cancel, n) has factors!
            # if (not isinstance(self.numerator, Mult) or
            #         term_to_cancel not in self.numerator.operands):
            #     raise ValueError("%s not in the numerator of %s"
            #                      % (term_to_cancel, self))
            if ((not isinstance(self.numerator, Mult)
                 and not isinstance(self.numerator, Exp)
                 and not isinstance(self.numerator, Neg))
                or (isinstance(self.numerator, Mult)
                    and term_to_cancel not in self.numerator.operands)
                or (isinstance(self.numerator, Exp)
                    and not (term_to_cancel == self.numerator.base
                             or (isinstance(term_to_cancel, Exp)
                                 and term_to_cancel.base == self.numerator.base )))
                or (isinstance(self.numerator, Neg)
                    and not (term_to_cancel == self.numerator.operand )
                    and not (isinstance(self.numerator.operand, Mult)
                             and term_to_cancel in self.numerator.operand.operands) ) ):
                raise ValueError("%s not in the numerator of %s"
                                 % (term_to_cancel, self))
            # Factor the term_to_cancel from the numerator to the left.
            expr = eq.update(expr.inner_expr().numerator.factorization(
                term_to_cancel, group_factors=True, group_remainder=True,
                preserve_all=True))
        if term_to_cancel != self.denominator:
            if (not isinstance(self.denominator, Mult) or
                    term_to_cancel not in self.denominator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 % (term_to_cancel, self))
            # Factor the term_to_cancel from the denominator to the left.
            expr = eq.update(expr.inner_expr().denominator.factorization(
                term_to_cancel, group_factors=True, group_remainder=True,
                preserve_all=True))
        if expr.numerator == expr.denominator == term_to_cancel:
            # Perhaps it reduced to the trivial x/x = 1 case via
            # auto-simplification.
            expr = eq.update(expr.cancelation(term_to_cancel))
            return eq.relation
        else:
            # (x*y) / (x*z) = y/z with possible automatic reductions
            # via 1 eliminations.
            from . import frac_cancel_left
            replacements = list(defaults.replacements)
            if expr.numerator == term_to_cancel:
                numer_prod = Mult(term_to_cancel, one)
                _y = one
                replacements.append(numer_prod.one_elimination(
                        1, preserve_expr=term_to_cancel))
            else:
                _y = expr.numerator.operands[1]
            if expr.denominator == term_to_cancel:
                denom_prod = Mult(term_to_cancel, one)
                _z = one
                replacements.append(denom_prod.one_elimination(
                        1, preserve_expr=term_to_cancel))
            else:
                _z = expr.denominator.operands[1]
            expr = eq.update(frac_cancel_left.instantiate(
                {x: term_to_cancel, y: _y, z: _z},
                 replacements=replacements, preserve_expr=expr))
            return eq.relation

    @equality_prover('deep_eliminated_ones', 'deep_eliminate_ones')
    def deep_one_eliminations(self, **defaults_config):
        '''
        Eliminate ones from the numerator, the denominator,
        and as a division by one.
        '''
        from proveit.numbers import one
        expr = self

        # A convenience to allow successive update to the equation
        # via transitivities (starting with self=self).
        eq = TransRelUpdater(self)

        for _i, operand in enumerate(self.operands):
            if hasattr(operand, 'deep_one_eliminations'):
                expr = eq.update(expr.inner_expr().operands[_i].
                                 deep_one_eliminations())

        if expr.denominator == one:
            expr = eq.update(expr.divide_by_one_elimination())
        return eq.relation

    @equality_prover('divide_by_one_eliminated', 'eliminate_divide_by_one')
    def divide_by_one_elimination(self, **defaults_config):
        from proveit.numbers import one
        from . import frac_one_denom
        if self.denominator != one:
            raise ValueError("'divide_by_one_elimination' is only applicable "
                             "if the denominator is precisely one.")
        return frac_one_denom.instantiate({x: self.numerator})

    def readily_factorable(self, factor):
        '''
        Return True iff 'factor' is factorable from 'self' in an
        obvious manner.  For this Div, it is readily factorable if
        it is readily factorable from the correxponding Mult:
            x/y = x*(y^{-1})
        '''
        return self.canonical_form().readily_factorable(factor)

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factors, pull="left",
                      group_factors=True, group_remainder=False,
                      **defaults_config):
        '''
        Return the proven factorization (equality with the factored
        form) from pulling the factor(s) from this division to the 
        "left" or "right".  If there are multiple occurrences, the first
        occurrence is used.
        If group_factors is True, the factors are
        grouped together as a sub-product.
        The group_remainder parameter ensures that the remainder is
        grouped together as a sub-product (which is only relevant
        if this division needed to be converted into a product in
        order to perform this factoring).

        Examples:

            [(a*b)/(c*d)].factorization((a/c))
            proves (a*b)/(c*d) = (a/c)*(b/d)
            [(a*b)/(c*d)].factorization((1/c))
            proves (a*b)/(c*d) = (1/c)*(a*b/d)
            [(a*b)/(c*d)].factorization(a, pull='right')
            proves (a*b)/(c*d) = (b/(c*d))*a
            [a/(c*d)].factorization(a, pull='right')
            proves a/(c*d) = (1/(c*d))*a
            [(a*b)/d].factorization((a/d), pull='right')
            proves (a*b)/d = b*(a/d)
        '''
        from proveit.numbers import one, Mult, readily_factorable
        from . import mult_frac_left, mult_frac_right, prod_of_fracs
        expr = self
        eq = TransRelUpdater(expr)
        if the_factors == self:
            return eq.relation # self = self
        if isinstance(the_factors, Div):
            the_factor_numer = the_factors.numerator
            the_factor_denom = the_factors.denominator
        else:
            the_factor_numer = the_factors
            the_factor_denom = one
        replacements = []
        # Factor out a fraction.
        if expr.denominator == the_factor_denom:
            # Factor (x/z) from (x*y)/z.
            # x or y may be 1.
            if the_factor_numer not in (one, expr.numerator):
                expr = eq.update(expr.inner_expr().numerator.factorization(
                        the_factors.numerator, pull=pull,
                        group_factors=True, group_remainder=True,
                        preserve_all=True))
            if pull == 'left':
                # factor (x*y)/z into (x/z)*y
                thm = mult_frac_left
                if the_factor_numer == one:
                    # factor y/z into (1/z)*y
                    _x = one
                    _y = expr.numerator
                    replacements.append(Mult(_x, _y).one_elimination(
                            0, preserve_all=True))
            else:
                # factor (x*y)/z into x*(y/z)
                thm = mult_frac_right
                if the_factor_numer == one:
                    # factor x/z into x*(1/z)
                    _x = expr.numerator
                    _y = one
                    replacements.append(Mult(_x, _y).one_elimination(
                            1, preserve_all=True))
            if the_factor_numer != one:
                assert expr.numerator.operands.num_entries() == 2
                _x = expr.numerator.operands.entries[0]
                _y = expr.numerator.operands.entries[1]
            _z = expr.denominator
            eq.update(thm.instantiate({x:_x, y:_y, z:_z},
                                      replacements=replacements))
        elif (readily_factorable(expr.numerator, the_factor_numer) and
              readily_factorable(expr.denominator, the_factor_denom)):
            # Factor (x*y)/(z*w) into (x/z)*(y/w).
            thm = prod_of_fracs
            if the_factor_denom not in (one, expr.denominator):
                expr = eq.update(expr.inner_expr().denominator.factorization(
                        the_factor_denom, pull=pull,
                        group_factors=True, preserve_all=True))
                assert expr.denominator.operands.num_entries() == 2
                _z = expr.denominator.operands.entries[0]
                _w = expr.denominator.operands.entries[1]
            elif (pull == 'left') == (the_factor_denom == one):
                # Factor (x*y)/w into x*(y/w).
                _z = one
                _w = expr.denominator
                replacements.append(Mult(_z, _w).one_elimination(
                        0, preserve_all=True))
            else:
                # Factor (x*y)/z into (x/z)*y.
                _z = expr.denominator
                _w = one
                replacements.append(Mult(_z, _w).one_elimination(
                        1, preserve_all=True))
            # Factor the numerator parts unless there is a 1 numerator.
            if the_factor_numer not in (one, expr.numerator):
                expr = eq.update(expr.inner_expr().numerator.factorization(
                        the_factor_numer, pull=pull,
                        group_factors=True, group_remainder=True,
                        preserve_all=True))
                assert expr.numerator.operands.num_entries() == 2
                # Factor (x*y)/(z*w) into (x/z)*(y/w)
                _x = expr.numerator.operands.entries[0]
                _y = expr.numerator.operands.entries[1]
            elif (pull == 'left') == (the_factor_numer == one):
                # Factor y/(z*w) into (1/z)*(y/w)
                _x = one
                _y = expr.numerator
                replacements.append(Mult(_x, _y).one_elimination(
                        0, preserve_all=True))
            else:
                # Factor x/(y*z) into (x/y)*(1/z)
                _x = expr.numerator
                _y = one
                replacements.append(Mult(_x, _y).one_elimination(
                        1, preserve_all=True))
            # create POSSIBLE replacements for inadvertently generated
            # fractions of the form _x/1 (i.e. _z = 1)
            # or _y/1 (i.e. _w = 1):
            if _z == one:
                replacements.append(frac(_x, _z).divide_by_one_elimination(
                        preserve_all=True))
            if _w == one:
                replacements.append(frac(_y, _w).divide_by_one_elimination(
                        preserve_all=True))

            eq.update(thm.instantiate({x:_x, y:_y, z:_z, w:_w},
                    replacements=replacements,
                    preserve_expr=expr))
        else:
            # As a last resort, convert this division to a 
            # multiplication and factor that.
            expr = eq.update(expr.reduction_to_mult())
            expr = eq.update(expr.factorization(
                    the_factors, pull=pull,
                    group_factors=group_factors, 
                    group_remainder=group_remainder))

        return eq.relation

    @equality_prover('distributed', 'distribute')
    def distribution(self, **defaults_config):
        r'''
        Distribute the denominator through the numerator, returning
        the equality that equates self to this new version.
        Examples:
            :math:`(a + b + c) / d = a / d + b / d + c / d`
            :math:`(a - b) / d = a / d - b / d`
            :math:`\left(\sum_x f(x)\right / y = \sum_x [f(x) / y]`
        Give any assumptions necessary to prove that the operands are
        in the Complex numbers so that the associative and commutation
        theorems are applicable.
        '''
        from proveit.numbers import Add, Sum, Neg
        from . import (distribute_frac_through_sum,
                       distribute_frac_through_subtract)
        if isinstance(self.numerator, Add):
            if (self.numerator.operands.is_double()
                    and isinstance(self.numerator.operands[1], Neg)):
                _x = self.numerator.operands[0]
                _y = self.numerator.operands[1].operand
                _z = self.denominator
                return distribute_frac_through_subtract.instantiate(
                        {x:_x, y:_y, z:_z})
            _x = self.numerator.operands
            _y = self.denominator
            _n = _x.num_elements()
            return distribute_frac_through_sum.instantiate(
                    {n: _n, x: _x, y: _y})
        elif isinstance(self.numerator, Sum):
            # Should deduce in Complex, but
            # distribute_through_summation doesn't have a domain
            # restriction right now because this is a little tricky.
            # To do.
            # deduce_in_complex(self.operands, assumptions)
            raise NotImplementedError(
                    "Distribution of division through summation not yet "
                    "implemented.")
            """
            y_etc_sub = self.numerator.indices
            Pop, Pop_sub = Function(
                P, self.numerator.indices), self.numerator.summand
            S_sub = self.numerator.domain
            dummy_var = safe_dummy_var(self)
            spec1 = distributefrac_through_summation.instantiate(
                {Pop: Pop_sub, S: S_sub, y_etc: y_etc_sub, z: dummy_var})
            return spec1.derive_conclusion().instantiate(
                {dummy_var: self.denominator})
            """
        else:
            raise Exception(
                "Unsupported operand type to distribute over: " +
                str(self.numerator.__class__))


    @equality_prover('neg_canceled', 'neg_cancel')
    def neg_cancelation(self, **defaults_config):
        '''
        Derive ((-x)/(-y)) = (x/y).
        '''
        from proveit.numbers import Neg
        from proveit.numbers.division import cancel_negations
        if not isinstance(self.numerator, Neg) or not(
                isinstance(self.denominator, Neg)):
            return cancel_negations.instantiate(
                    {x:self.numerator.operator,
                     y:self.denominator.operator})

    @equality_prover('neg_extracted', 'neg_extract')
    def neg_extraction(self, neg_loc=None, **defaults_config):
        '''
        Factor out a negation from the numerator (default) or
        denominator (specified with neg_loc='denominator'),
        returning the equality between the original self and the
        resulting fraction with the negative (Neg) out in front.
        For example, given expr = (-x)/y, then expr.neg_extraction()
        (with suitable assumptions or info about x and y) returns:
        |- (-x)/y = -(x/y).
        The theorems being applied require numerator and denom elements
        to be Complex with denom != 0. If neg_loc is None, attempts
        to find a suitable Neg component to extract.
        Implemented in a naive way for cases in which the Neg is one
        of several factors in the numerator or denominator, giving for
        example:
        |- (x(-z))/y = -((xz)/y)
        '''
        from proveit.numbers import Mult, Neg
        if neg_loc is None:
            # Check if entire numerator is a Neg
            if isinstance(self.numerator, Neg):
                neg_loc = 'numerator'
            elif isinstance(self.numerator, Mult):
                # check if one of the numerator's factors is a Neg:
                for factor in self.numerator.factors:
                    if isinstance(factor, Neg):
                        neg_loc = 'numerator_factor'
                        numerator_factor = factor
                        break
            elif isinstance(self.denominator, Neg):
                neg_loc = 'denominator'
            elif isinstance(self.denominator, Mult):
                # check if one of the denominator's factors is a Neg:
                for factor in self.denominator.factors:
                    if isinstance(factor, Neg):
                        neg_loc = 'denominator_factor'
                        denominator_factor = factor
                        break
                if neg_loc is None:
                    raise ValueError(
                            "No Neg expression component found to extract. "
                            "The expression supplied was: {}".format(self))
            else:
                raise ValueError(
                        "No Neg expression component found to extract. "
                        "The expression supplied was: {}".format(self))
        if neg_loc == 'numerator' and not isinstance(self.numerator, Neg):
            raise ValueError(
                    "The numerator version of Div.neg_extraction() can "
                    "only be applied if the entire numerator is negated "
                    "(i.e. inside a Neg). The numerator supplied was: "
                    "{}".format(self.numerator))
        if neg_loc == 'denominator' and not isinstance(self.denominator, Neg):
            raise ValueError(
                    "The denominator version of Div.neg_extraction() can "
                    "only be applied if the entire denominator is negated "
                    "(i.e. inside a Neg). The denominator supplied was: "
                    "{}".format(self.denominator))
        # add error checks here for neg_loc values 'numerator_factor'
        # and 'denominator_factor'
        import proveit.numbers.division as div_pkg

        # Case (1) Neg(x)/y = Neg(x/y)
        if neg_loc == 'numerator':
            thm = div_pkg.neg_frac_neg_numerator
            _x, _y = thm.instance_params
            _x_sub = self.numerator.operand
            _y_sub = self.denominator
            return thm.instantiate(
                    {_x: _x_sub, _y: _y_sub})

        # Case (2) x/Neg(y) = Neg(x/y)
        if neg_loc == 'denominator':
            thm = div_pkg.neg_frac_neg_denominator
            _x, _y = thm.instance_params
            _x_sub = self.numerator
            _y_sub = self.denominator.operand
            return thm.instantiate(
                    {_x: _x_sub, _y: _y_sub})

        # Case (3) Neg is a factor in the numerator
        # -- first pull the Neg out in front of the numerator
        # -- then re-call the exp_extraction() method
        if neg_loc == 'numerator_factor':
            intermed_equality = (
                    self.inner_expr().numerator.neg_simplifications(
                        preserve_all=True))
            return intermed_equality.inner_expr().rhs.neg_extract()

        # # Case (4) Neg is a factor in the denominator
        # -- first pull the Neg out in front of the numerator
        # -- then re-call the exp_extraction() method
        if neg_loc == 'denominator_factor':
            intermed_equality = (
                    self.inner_expr().denominator.neg_simplifications(
                        preserve_all=True))
            return intermed_equality.inner_expr().rhs.neg_extract()

        # Other cases here?
        # Consider more generality by allowing user to specify the
        # neg_loc = 'numerator/denominator_factor' and allowing
        # a 0-based index for the factor. Related: see more general
        # neg_frac_neg theorems in division pkg.


    @equality_prover('combined_exponents', 'combine_exponents')
    def exponent_combination(self, start_idx=None, end_idx=None,
                             **defaults_config):
        '''
        Equates $a^m/a^n$ to $a^{m-n} or
        $a^c/b^c$ to $(a/b)^c$.
        '''
        from proveit.numbers import Exp
        from proveit.numbers.exponentiation import (
            quotient_of_posnat_powers, quotient_of_pos_powers,
            quotient_of_real_powers, quotient_of_complex_powers)
        if (isinstance(self.numerator, Exp)
                and isinstance(self.denominator, Exp)):
            if self.numerator.base == self.denominator.base:
                # Same base: (a^b/a^c) = a^{b-c}
                same_base = self.numerator.bas
                exponents = (self.numerator.exponent,
                             self.denominator.exponent)
                # Find out the known type of the exponents.
                possible_exponent_types = [NaturalPos, RealPos, Real,
                                           Complex]
                for exponent in exponents:
                    exp_ns = readily_provable_number_set(exponent,
                                                         default=Complex)
                    while len(possible_exponent_types) > 1:
                        exponent_type = possible_exponent_types[0]
                        if exponent_type.readily_includes(exp_ns):
                            # This type is known for this exponent.
                            break
                        # We've eliminated a type from being known.
                        possible_exponent_types.pop(0)
                known_exponent_type = possible_exponent_types[0]

                if known_exponent_type == NaturalPos:
                    _m, _n = exponents
                    return quotient_of_posnat_powers.instantiate(
                        {a: same_base, m: _m, n: _n})
                else:
                    _b, _c = exponents
                    if known_exponent_type == RealPos:
                        thm = quotient_of_pos_powers
                    elif known_exponent_type == Real:
                        thm = quotient_of_real_powers
                    else:  # Complex is the default
                        thm = quotient_of_complex_powers
                    thm.instantiate({a: same_base, b: _b, c: _c})

            elif self.numerator.exponent == self.denominator.exponent:
                # Same exponent: (a^c/b^c) = (a/b)^c
                same_exponent = self.numerator.exponent
                bases = (self.numerator.base, self.denominator.base)
                # Combining the exponents in this case is the reverse
                # of disibuting an exponent.
                quotient = Div(*bases).with_matching_style(self)
                exp = Exp(quotient, same_exponent)
                return exp.distribution().derive_reversed()
        else:
            raise NotImplementedError("Need to implement degenerate cases "
                                      "of a^b/a and a/a^b.")

    def readily_not_equal(self, other):
        '''
        Return True iff self and other are numeric rationals (at least
        in canonical form) that are not equal to each other.
        '''
        from proveit.numbers import not_equal_numeric_rationals
        return not_equal_numeric_rationals(self, other.canonical_form())

    @relation_prover
    def deduce_not_equal(self, other, **defaults_config):
        '''
        Prove and return self ≠ other if self and other are numeric
        rational.
        '''
        from proveit.numbers import (
                is_numeric_rational, deduce_not_equal_numeric_rationals)
        if not (is_numeric_rational(self) and is_numeric_rational(other)):
            raise NotImplementedError(
                    "Divide.deduce_not_equal only handles the case of "
                    "numeric rationals.  Given %s and %s"%(self, other))
        return deduce_not_equal_numeric_rationals(self, other)

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem.
        '''
        from proveit import a, b
        from proveit.numbers import Less, zero
        import proveit.numbers.division as div_pkg

        thm = None
        if number_set == ZeroSet:
            # prove 0/x in {0}; while we are at it, prove 0/x = 0
            div_pkg.frac_zero_numer.instantiate({x:self.denominator})
            thm = div_pkg.frac_in_zero_set
        elif number_set == Rational:
            thm = div_pkg.div_rational_closure
        elif number_set == RationalNonZero:
            thm = div_pkg.div_rational_nonzero_closure
        elif number_set == RationalPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_rational_pos_from_double_neg
            else:
                thm = div_pkg.div_rational_pos_closure
        elif number_set == RationalNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_rational_neg_from_neg_denom
            else:
                thm = div_pkg.div_rational_neg_from_neg_numer
        elif number_set == RationalNonNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_rational_nonneg_from_double_neg
            else:
                thm = div_pkg.div_rational_nonneg_closure
        elif number_set == RationalNonPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_rational_nonpos_from_neg_denom
            else:
                thm = div_pkg.div_rational_nonpos_from_nonpos_numer
        elif number_set == Real:
            thm = div_pkg.div_real_closure
        elif number_set == RealNonZero:
            thm = div_pkg.div_real_nonzero_closure
        elif number_set == RealPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_real_pos_from_double_neg
            else:
                thm = div_pkg.div_real_pos_closure
        elif number_set == RealNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_real_neg_from_neg_denom
            else:
                thm = div_pkg.div_real_neg_from_neg_numer
        elif number_set == RealNonNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_real_nonneg_from_double_neg
            else:
                thm = div_pkg.div_real_nonneg_closure
        elif number_set == RealNonPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).readily_provable():
                thm = div_pkg.div_real_nonpos_from_neg_denom
            else:
                thm = div_pkg.div_real_nonpos_from_nonpos_numer
        elif number_set == ComplexNonZero:
            thm = div_pkg.div_complex_nonzero_closure
        elif number_set == Complex:
            thm = div_pkg.div_complex_closure
        if thm is not None:
            return thm.instantiate({a: self.numerator, b: self.denominator})
        raise NotImplementedError(
            "'Div.deduce_in_number_set()' not implemented for the %s set"
            % str(number_set))

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        numer_ns = readily_provable_number_set(self.numerator)
        denom_ns = readily_provable_number_set(self.denominator)
        if numer_ns is None or denom_ns is None: return None
        if numer_ns == ZeroSet: return ZeroSet
        if RationalPos.readily_includes(numer_ns) and (
                RationalPos.readily_includes(denom_ns)):
            return RationalPos
        if RationalNeg.readily_includes(numer_ns) and (
                RationalNeg.readily_includes(denom_ns)):
            return RationalPos
        if RationalNeg.readily_includes(numer_ns) and (
                RationalPos.readily_includes(denom_ns)):
            return RationalNeg
        if RationalPos.readily_includes(numer_ns) and (
                RationalNeg.readily_includes(denom_ns)):
            return RationalNeg
        if (RationalNonNeg.readily_includes(numer_ns)
                and RationalPos.readily_includes(denom_ns)):
            return RationalNonNeg
        if (RationalNonPos.readily_includes(numer_ns)
                and RationalPos.readily_includes(denom_ns)):
            return RationalNonPos
        if (RationalNonNeg.readily_includes(numer_ns)
                and RationalNeg.readily_includes(denom_ns)):
            return RationalNonPos
        if (RationalNonPos.readily_includes(numer_ns)
                and RationalNeg.readily_includes(denom_ns)):
            return RationalNonNeg
        if (RationalNonZero.readily_includes(numer_ns) and
               RationalNonZero.readily_includes(denom_ns)):
            return RationalNonZero
        if Rational.readily_includes(numer_ns) and (
                RationalNonZero.readily_includes(denom_ns)):
            return Rational
        if RealPos.readily_includes(numer_ns) and (
                RealPos.readily_includes(denom_ns)):
            return RealPos
        if RealNeg.readily_includes(numer_ns) and (
                RealNeg.readily_includes(denom_ns)):
            return RealPos
        if RealPos.readily_includes(numer_ns) and (
                RealNeg.readily_includes(denom_ns)):
            return RealNeg
        if RealNeg.readily_includes(numer_ns) and (
                RealPos.readily_includes(denom_ns)):
            return RealNeg
        if RealNonNeg.readily_includes(numer_ns) and (
                RealPos.readily_includes(denom_ns)):
            return RealNonNeg
        if RealNonPos.readily_includes(numer_ns) and (
                RealPos.readily_includes(denom_ns)):
            return RealNonPos
        if RealNonNeg.readily_includes(numer_ns) and (
                RealNeg.readily_includes(denom_ns)):
            return RealNonPos
        if RealNonPos.readily_includes(numer_ns) and (
                RealNeg.readily_includes(denom_ns)):
            return RealNonNeg
        if Real.readily_includes(numer_ns) and (
                RealNonZero.readily_includes(denom_ns)):
            return Real
        if RealNonZero.readily_includes(numer_ns) and (
                RealNonZero.readily_includes(denom_ns)):
            return RealNonZero
        if Real.readily_includes(numer_ns) and (
                RealNonZero.readily_includes(denom_ns)):
            return Real
        if (ComplexNonZero.readily_includes(numer_ns)
                and ComplexNonZero.readily_includes(denom_ns)):
            return ComplexNonZero
        return Complex

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        Deduce a bound of this division (fraction) given a bound on
        either the numerator or the denominator.
        '''
        from proveit.numbers import NumberOrderingRelation
        if isinstance(operand_relation, Judgment):
            operand_relation = operand_relation.expr
        if not isinstance(operand_relation, NumberOrderingRelation):
            raise TypeError("'operand_relation' expected to be a number "
                            "relation (<, >, ≤, or ≥)")
        lhs = operand_relation.lhs
        if lhs == self.numerator:
            return self.bound_via_numerator_bound(operand_relation)
        elif lhs == self.denominator:
            return self.bound_via_denominator_bound(operand_relation)
        else:
            raise ValueError("Left side of %s expected to be the numerator "
                             "or denominator of %s"%(operand_relation, self))

    @relation_prover
    def bound_via_numerator_bound(self, relation, **defaults_config):
        '''
        Given a relation applicable to the numerator,  bound this
        division accordingly.  For example,
        if self is "a / b" and the relation is a < x
        return (a / b) < (x / b), provided b > 0.

        Also see NumberOperation.deduce_bound.
        '''
        from proveit.numbers import zero, Less, LessEq, greater
        from . import (strong_div_from_numer_bound__pos_denom,
                       weak_div_from_numer_bound__pos_denom,
                       strong_div_from_numer_bound__neg_denom,
                       weak_div_from_numer_bound__neg_denom)
        if isinstance(relation, Judgment):
            relation = relation.expr
        if not (isinstance(relation, Less) or
                isinstance(relation, LessEq)):
            raise TypeError("relation is expected to be Less "
                            "or LessEq number relations, not %s"
                            %relation)
        if self.numerator not in relation.operands:
            raise ValueError("relation is expected to involve the "
                             "numerator of %s.  %s does not."
                             %(self, relation))
        _a = self.denominator
        _x = relation.normal_lhs
        _y = relation.normal_rhs
        try:
            deduce_number_set(self.denominator)
        except UnsatisfiedPrerequisites:
            pass
        if greater(self.denominator, zero).readily_provable():
            if isinstance(relation, Less):
                bound = strong_div_from_numer_bound__pos_denom.instantiate(
                        {a: _a, x: _x, y: _y})
            elif isinstance(relation, LessEq):
                bound =  weak_div_from_numer_bound__pos_denom.instantiate(
                        {a: _a, x: _x, y: _y})
        elif Less(self.denominator, zero).readily_provable():
            if isinstance(relation, Less):
                bound =  strong_div_from_numer_bound__neg_denom.instantiate(
                        {a: _a, x: _x, y: _y})
            elif isinstance(relation, LessEq):
                bound =  weak_div_from_numer_bound__neg_denom.instantiate(
                        {a: _a, x: _x, y: _y})
        else:
            raise UnsatisfiedPrerequisites(
                    "We must know whether the denominator of %s "
                    "is positive or negative before we can use "
                    "'bound_via_numerator_bound'."%self)
        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound

    @relation_prover
    def bound_via_denominator_bound(self, relation, **defaults_config):
        '''
        Given a relation applicable to the numerator,  bound this
        division accordingly.  For example,
        if self is "a / b" and the relation is b > y
        return (a / b) < (a / y), provided a, b, and y are positive.

        Also see NumberOperation.deduce_bound.
        '''
        from proveit.numbers import zero, Less, LessEq, greater, greater_eq
        from . import (strong_div_from_denom_bound__all_pos,
                       weak_div_from_denom_bound__all_pos,
                       strong_div_from_denom_bound__all_neg,
                       weak_div_from_denom_bound__all_neg,
                       strong_div_from_denom_bound__neg_over_pos,
                       weak_div_from_denom_bound__neg_over_pos,
                       strong_div_from_denom_bound__pos_over_neg,
                       weak_div_from_denom_bound__pos_over_neg)
        if isinstance(relation, Judgment):
            relation = relation.expr
        if not (isinstance(relation, Less) or
                isinstance(relation, LessEq)):
            raise TypeError("relation is expected to be Less "
                            "or LessEq number relations, not %s"
                            %relation)
        if self.denominator not in relation.operands:
            raise ValueError("relation is expected to involve the "
                             "denominator of %s.  %s does not."
                             %(self, relation))
        _a = self.numerator
        _x = relation.normal_lhs
        _y = relation.normal_rhs
        try:
            # Ensure that we relate both _x and _y to zero by knowing
            # one of these.
            ordering = LessEq.sort((_x, _y, zero))
            ordering.operands[0].apply_transitivity(ordering.operands[1])
        except:
            pass # We'll generate an appropriate error below.
        try:
            deduce_number_set(self.numerator)
            deduce_number_set(self.denominator)
        except UnsatisfiedPrerequisites:
            pass
        pos_numer = greater_eq(self.numerator, zero).readily_provable()
        neg_numer = LessEq(self.numerator, zero).readily_provable()
        pos_denom = greater(self.denominator, zero).readily_provable()
        neg_denom = Less(self.denominator, zero).readily_provable()
        if not (pos_numer or neg_numer) or not (pos_denom or neg_denom):
            raise UnsatisfiedPrerequisites(
                    "We must know the sign of the numerator and "
                    "denominator of %s before we can use "
                    "'bound_via_denominator_bound'."%self)
        if pos_numer and pos_denom:
            if isinstance(relation, Less):
                bound = strong_div_from_denom_bound__all_pos.instantiate(
                        {a: _a, x: _x, y: _y})
            elif isinstance(relation, LessEq):
                bound = weak_div_from_denom_bound__all_pos.instantiate(
                        {a: _a, x: _x, y: _y})
        elif neg_numer and neg_denom:
            if isinstance(relation, Less):
                bound = strong_div_from_denom_bound__all_neg.instantiate(
                        {a: _a, x: _x, y: _y})
            elif isinstance(relation, LessEq):
                bound = weak_div_from_denom_bound__all_neg.instantiate(
                        {a: _a, x: _x, y: _y})
        elif pos_numer and neg_denom:
            if isinstance(relation, Less):
                bound = strong_div_from_denom_bound__pos_over_neg.instantiate(
                        {a: _a, x: _x, y: _y})
            elif isinstance(relation, LessEq):
                bound = weak_div_from_denom_bound__pos_over_neg.instantiate(
                        {a: _a, x: _x, y: _y})
        elif neg_numer and pos_denom:
            if isinstance(relation, Less):
                bound = strong_div_from_denom_bound__neg_over_pos.instantiate(
                        {a: _a, x: _x, y: _y})
            elif isinstance(relation, LessEq):
                bound = weak_div_from_denom_bound__neg_over_pos.instantiate(
                        {a: _a, x: _x, y: _y})
        else:
            raise UnsatisfiedPrerequisites(
                    "We must know whether or not the denominator of %s "
                    "is positive or negative before we can use "
                    "'bound_via_denominator_bound'."%self)
        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound


def frac(numer, denom):
    return Div(numer, denom)
