from proveit import (Judgment, Expression, Literal, Operation,
                     maybe_fenced_latex, defaults,
                     Function, ExprTuple, InnerExpr, USE_DEFAULTS,
                     UnsatisfiedPrerequisites, relation_prover,
                     equality_prover, SimplificationDirectives)
from proveit import TransRelUpdater
from proveit import a, b, c, m, n, w, x, y, z
from proveit.logic import Equals, NotEquals, InSet
from proveit.numbers import zero, NumberOperation, is_literal_int
from proveit.numbers import NumberOperation, deduce_number_set
from proveit.numbers.number_sets import (
    Natural, NaturalPos,
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
            factor_negation = True, reduce_zero_numerator = True)

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
                                     is_literal_rational,
                                     simplified_rational_expr)
        if is_literal_rational(self):
            # Return the irreducible rational.
            return simplified_rational_expr(self.numerator.as_int(),
                                            self.denominator.as_int())
        as_mult = Mult(self.numerator, Exp(self.denominator, Neg(one)))
        return as_mult.canonical_form()

    def _deduce_equality(self, equality):
        '''
        Prove that this Divide is equal to an expression that has the
        same canonical form.
        '''
        from proveit.numbers import one, Mult
        with defaults.temporary() as tmp_defaults:
            tmp_defaults.auto_simplify = False # We want manual...
            tmp_defaults.replacements = set()  # control.
            # Need to prove (a / b) = (c / d)
            _a, _b = self.numerator, self.denominator
            other = equality.rhs
            # Start with (a*d) = (c*b)
            if isinstance(other, Div):
                _c, _d = other.numerator, other.denominator
                known_eq = Equals(Mult(_a, _d), Mult(_c, _b))
                _bd = Mult(_b, _d)
            else:
                _c, _d = other, one # d=1
                known_eq = Equals(_a, Mult(_c, _b))
                _bd = _b
            known_eq = known_eq.prove()
            # (a*d)/(b*d) = (c*b)/(b*d)
            known_eq = known_eq.divide_both_sides(_bd)
            # (a/b) = (c/d)
            if _d != one:
                known_eq.inner_expr().lhs.cancelation(_d)
            known_eq.inner_expr().rhs.cancelation(_b)
            return known_eq

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Divide
        expression assuming the operands have been simplified.

        Specifically, cancels common factors and eliminates ones.
        '''
        from proveit.logic import is_irreducible_value
        from proveit.numbers import one, Neg
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)

        # perform cancelations where possible
        expr = eq.update(expr.cancelations(preserve_all=True))
        if not isinstance(expr, Div):
            # complete cancelation.
            return eq.relation

        if self.is_irreducible_value():
            # already irreducible
            return Equals(self, self).conclude_via_reflexivity()

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
            if is_irreducible_value(canonical_form):
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
            if ((expr.numerator==zero or Equals(expr.numerator, zero).proven())
                and NotEquals(expr.denominator, zero).proven()):
                # we have something like 0/x so reduce to 0
                expr = eq.update(expr.zero_numerator_reduction())
        
        # finally, check if we have something like (x/(y/z))
        # but! remember to check here if we still even have a Div expr
        # b/c some of the work above might have changed it to
        # something else!
        if (isinstance(expr, Div)
            and isinstance(expr.denominator, Div)
            and NotEquals(expr.denominator.numerator, zero).proven()
            and NotEquals(expr.denominator.denominator, zero).prove() ):
            expr = eq.update(expr.div_in_denominator_reduction())

        return eq.relation

    def is_irreducible_value(self):
        '''
        This needs work, but we know that 1/x is irreducible if
        x is irreducible, not a negation, not 0 and not 1.
        '''
        from proveit.numbers import simplified_rational_expr
        if is_literal_int(self.numerator) and is_literal_int(self.denominator):
            # This is an irreducible rational if and only if it is the
            # same as the corresponding 'simiplified_rational_expr'.
            # (which divides out the gcd and extracts any negation).
            numer_int = self.numerator.as_int()
            denom_int = self.denominator.as_int()
            return self == simplified_rational_expr(numer_int, denom_int)
        return False
            
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


    @equality_prover('all_canceled', 'all_cancel')
    def cancelations(self, **defaults_config):
        '''
        Deduce and return an equality between self and a form in which
        all simple division cancellations are performed.
        '''
        from proveit.numbers import Mult
        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self)

        numer_factors = (self.numerator.operands if
                         isinstance(self.numerator, Mult) else
                         [self.numerator])
        denom_factors = (self.denominator.operands if
                         isinstance(self.denominator, Mult) else
                         [self.denominator])
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
        from proveit.numbers import Mult, one
        expr = self
        eq = TransRelUpdater(expr)

        if self.numerator == self.denominator == term_to_cancel:
            # x/x = 1
            from . import frac_cancel_complete
            return frac_cancel_complete.instantiate(
                {x: term_to_cancel})

        if term_to_cancel != self.numerator:
            # try to catch Exp objects here as well?
            # after all, Exp(term_to_cancel, n) has factors!
            if (not isinstance(self.numerator, Mult) or
                    term_to_cancel not in self.numerator.operands):
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

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factors, pull="left",
                      group_factors=True, group_remainder=True,
                      **defaults_config):
        '''
        Return the proven factorization (equality with the factored
        form) from pulling the factor(s) from this division to the 
        "left" or "right".  If there are multiple occurrences, the first
        occurrence is used.
        If group_factors is True, the factors are
        grouped together as a sub-product.
        The group_remainder parameter is not relevant here but kept
        for consistency with other factorization methods.

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
        from proveit.numbers import one, Mult
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
        else:
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
        from proveit.numbers.division import (
                neg_frac_neg_numerator, neg_frac_neg_denominator,
                neg_frac_neg_numerator_gen, neg_frac_neg_denominator_gen)

        # Case (1) Neg(x)/y = Neg(x/y)
        if neg_loc == 'numerator':
            _x, _y = neg_frac_neg_numerator.instance_params
            _x_sub = self.numerator.operand
            _y_sub = self.denominator
            return neg_frac_neg_numerator.instantiate(
                    {_x: _x_sub, _y: _y_sub})

        # Case (2) x/Neg(y) = Neg(x/y)
        if neg_loc == 'denominator':
            _x, _y = neg_frac_neg_denominator.instance_params
            _x_sub = self.numerator
            _y_sub = self.denominator.operand
            return neg_frac_neg_denominator.instantiate(
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
        from proveit.logic import InSet
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
                    deduce_number_set(exponent)
                    while len(possible_exponent_types) > 1:
                        exponent_type = possible_exponent_types[0]
                        if InSet(exponent, exponent_type).proven():
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

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem.
        '''
        from proveit import a, b
        from proveit.numbers import Less, zero
        from proveit.numbers.division import (
            div_rational_closure, div_rational_nonzero_closure,
            div_rational_pos_closure,
            div_rational_pos_from_double_neg,
            div_rational_neg_from_neg_denom,
            div_rational_neg_from_neg_numer,
            div_rational_nonneg_closure,
            div_rational_nonneg_from_double_neg,
            div_rational_nonpos_from_neg_denom,
            div_rational_nonpos_from_nonpos_numer,
            div_real_closure, div_real_nonzero_closure,
            div_real_pos_closure,
            div_real_pos_from_double_neg,
            div_real_neg_from_neg_denom,
            div_real_neg_from_neg_numer,
            div_real_nonneg_closure,
            div_real_nonneg_from_double_neg,
            div_real_nonpos_from_neg_denom,
            div_real_nonpos_from_nonpos_numer,
            div_complex_nonzero_closure,
            div_complex_closure)

        thm = None
        if number_set == Rational:
            thm = div_rational_closure
        elif number_set == RationalNonZero:
            thm = div_rational_nonzero_closure
        elif number_set == RationalPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_rational_pos_from_double_neg
            else:
                thm = div_rational_pos_closure
        elif number_set == RationalNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_rational_neg_from_neg_denom
            else:
                thm = div_rational_neg_from_neg_numer
        elif number_set == RationalNonNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_rational_nonneg_from_double_neg
            else:
                thm = div_rational_nonneg_closure
        elif number_set == RationalNonPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_rational_nonpos_from_neg_denom
            else:
                thm = div_rational_nonpos_from_neg_numer
        elif number_set == Real:
            thm = div_real_closure
        elif number_set == RealNonZero:
            thm = div_real_nonzero_closure
        elif number_set == RealPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_real_pos_from_double_neg
            else:
                thm = div_real_pos_closure
        elif number_set == RealNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_real_neg_from_neg_denom
            else:
                thm = div_real_neg_from_neg_numer
        elif number_set == RealNonNeg:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_real_nonneg_from_double_neg
            else:
                thm = div_real_nonneg_closure
        elif number_set == RealNonPos:
            deduce_number_set(self.denominator)
            if Less(self.denominator, zero).proven():
                thm = div_real_nonpos_from_neg_denom
            else:
                thm = div_real_nonpos_from_nonpos_numer
        elif number_set == ComplexNonZero:
            thm = div_complex_nonzero_closure
        elif number_set == Complex:
            thm = div_complex_closure
        if thm is not None:
            return thm.instantiate({a: self.numerator, b: self.denominator})
        raise NotImplementedError(
            "'Div.deduce_in_number_set()' not implemented for the %s set"
            % str(number_set))

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most
        restrictive standard number set we can readily know.
        '''
        numer_ns = deduce_number_set(self.numerator).domain
        denom_ns = deduce_number_set(self.denominator).domain
        if RationalPos.includes(numer_ns) and RationalPos.includes(denom_ns):
            return self.deduce_in_number_set(RationalPos)
        if RationalNeg.includes(numer_ns) and RationalNeg.includes(denom_ns):
            return self.deduce_in_number_set(RationalPos)
        if RationalNeg.includes(numer_ns) and RationalPos.includes(denom_ns):
            return self.deduce_in_number_set(RationalNeg)
        if RationalPos.includes(numer_ns) and RationalNeg.includes(denom_ns):
            return self.deduce_in_number_set(RationalNeg)
        if (RationalNonNeg.includes(numer_ns)
                and RationalPos.includes(denom_ns)):
            return self.deduce_in_number_set(RationalNonNeg)
        if (RationalNonPos.includes(numer_ns)
                and RationalPos.includes(denom_ns)):
            return self.deduce_in_number_set(RationalNonPos)
        if (RationalNonNeg.includes(numer_ns)
                and RationalNeg.includes(denom_ns)):
            return self.deduce_in_number_set(RationalNonPos)
        if (RationalNonPos.includes(numer_ns)
                and RationalNeg.includes(denom_ns)):
            return self.deduce_in_number_set(RationalNonNeg)
        if (RationalNonZero.includes(numer_ns) and
               RationalNonZero.includes(denom_ns)):
            return self.deduce_in_number_set(RationalNonZero)
        if Rational.includes(numer_ns) and RationalNonZero.includes(denom_ns):
            return self.deduce_in_number_set(Rational)
        if RealPos.includes(numer_ns) and RealPos.includes(denom_ns):
            return self.deduce_in_number_set(RealPos)
        if RealNeg.includes(numer_ns) and RealNeg.includes(denom_ns):
            return self.deduce_in_number_set(RealPos)
        if RealPos.includes(numer_ns) and RealNeg.includes(denom_ns):
            return self.deduce_in_number_set(RealNeg)
        if RealNeg.includes(numer_ns) and RealPos.includes(denom_ns):
            return self.deduce_in_number_set(RealNeg)
        if RealNonNeg.includes(numer_ns) and RealPos.includes(denom_ns):
            return self.deduce_in_number_set(RealNonNeg)
        if RealNonPos.includes(numer_ns) and RealPos.includes(denom_ns):
            return self.deduce_in_number_set(RealNonPos)
        if RealNonNeg.includes(numer_ns) and RealNeg.includes(denom_ns):
            return self.deduce_in_number_set(RealNonPos)
        if RealNonPos.includes(numer_ns) and RealNeg.includes(denom_ns):
            return self.deduce_in_number_set(RealNonNeg)
        if Real.includes(numer_ns) and RealNonZero.includes(denom_ns):
            return self.deduce_in_number_set(Real)
        if RealNonZero.includes(numer_ns) and RealNonZero.includes(denom_ns):
            return self.deduce_in_number_set(RealNonZero)
        if Real.includes(numer_ns) and RealNonZero.includes(denom_ns):
            return self.deduce_in_number_set(Real)
        if (ComplexNonZero.includes(numer_ns)
                and ComplexNonZero.includes(denom_ns)):
            return self.deduce_in_number_set(ComplexNonZero)
        return self.deduce_in_number_set(Complex)

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
        if greater(self.denominator, zero).proven():
            if isinstance(relation, Less):
                bound = strong_div_from_numer_bound__pos_denom.instantiate(
                        {a: _a, x: _x, y: _y})
            elif isinstance(relation, LessEq):
                bound =  weak_div_from_numer_bound__pos_denom.instantiate(
                        {a: _a, x: _x, y: _y})
        elif Less(self.denominator, zero).proven():
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
        pos_numer = greater_eq(self.numerator, zero).proven()
        neg_numer = LessEq(self.numerator, zero).proven()
        pos_denom = greater(self.denominator, zero).proven()
        neg_denom = Less(self.denominator, zero).proven()
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
