from proveit import (Literal, maybe_fenced_latex, Operation, InnerExpr,
                     StyleOptions, USE_DEFAULTS)
from proveit import TransRelUpdater
from proveit._common_ import a, b, c, m, n, x, y, z


class Div(Operation):
    # operator of the Add operation
    _operator_ = Literal(
        string_format='/',
        latex_format=r'\div',
        theory=__file__)

    def __init__(self, numerator, denominator):
        r'''
        Divide two operands.
        '''
        Operation.__init__(self, Div._operator_, [numerator, denominator],
                           styles={'division': 'inline'})
        self.numerator = self.operands[0]
        self.denominator = self.operands[1]

    def style_options(self):
        options = StyleOptions(self)
        options.add(
            'division',
            "'inline': uses '/'; 'fraction': numerator over the denominator")
        return options

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
            return Operation.latex(self, **kwargs)  # normal division

    def remake_constructor(self):
        if self.get_style('division') == 'fraction':
            return 'frac'  # use a different constructor if using the fraction style
        return Operation.remake_constructor(self)

    def do_reduced_simplification(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Perform simplifications of a Divide expression after the
        operands have individually been simplified.
        Cancels common factors...
        '''
        from proveit.numbers import one
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr, assumptions)

        # perform cancelations where possible
        expr = eq.update(expr.cancelations(assumptions))
        if not isinstance(expr, Div):
            # complete cancelation.
            return eq.relation

        if self.denominator == one:
            # eliminate division by one
            eq.update(expr.eliminate_divide_by_one(assumptions))
            return eq.relation  # no more division simplifications.

        return eq.relation

    """
    # outdated.  obsolete.
    def combine_exponents(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import frac_int_exp, frac_nat_pos_exp
        from proveit.numbers import Exp
        if isinstance(self.numerator, Exp) and isinstance(self.denominator, Exp):
            if self.numerator.exponent == self.denominator.exponent:
                exponent = self.numerator.exponent
                try:
                    return frac_nat_pos_exp.instantiate({n:exponent}).instantiate({a:self.numerator.base, b:self.denominator.base})
                except:
                    return frac_int_exp.instantiate({n:exponent}).instantiate({a:self.numerator.base, b:self.denominator.base})
        raise Exception('Unable to combine exponents of this fraction')
    """

    def cancelations(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        all simple division cancellations are performed.
        '''
        from proveit.numbers import Mult
        expr = self

        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        numer_factors = (self.numerator.operands if
                         isinstance(self.numerator, Mult) else
                         [self.numerator])
        denom_factors = (self.denominator.operands if
                         isinstance(self.denominator, Mult) else
                         [self.denominator])
        denom_factors_set = set(denom_factors)

        for numer_factor in numer_factors:
            if numer_factor in denom_factors_set:
                expr = eq.update(expr.cancelation(numer_factor, assumptions))
                denom_factors_set.remove(numer_factor)

        return eq.relation

    def cancelation(self, term_to_cancel, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        the given operand has been canceled on the numerator and
        denominator.  For example,
        [(a*b)/(b*c)].cancelation(b) would return
        (a*b)/(b*c) = a / c
        '''
        from proveit.numbers import Mult
        expr = self
        eq = TransRelUpdater(expr, assumptions)

        if self.numerator == self.denominator == term_to_cancel:
            # x/x = 1
            from ._theorems_ import frac_cancel_complete
            return frac_cancel_complete.instantiate(
                {x: term_to_cancel}).checked(assumptions)

        if term_to_cancel != self.numerator:
            if (not isinstance(self.numerator, Mult) or
                    term_to_cancel not in self.numerator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 % (term_to_cancel, self))
            # Factor the term_to_cancel from the numerator to the left.
            expr = eq.update(expr.inner_expr().numerator.factorization(
                term_to_cancel, group_factor=True, group_remainder=True,
                assumptions=assumptions))
        if term_to_cancel != self.denominator:
            if (not isinstance(self.denominator, Mult) or
                    term_to_cancel not in self.denominator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 % (term_to_cancel, self))
            # Factor the term_to_cancel from the denominator to the left.
            expr = eq.update(expr.inner_expr().denominator.factorization(
                term_to_cancel, group_factor=True, group_remainder=True,
                assumptions=assumptions))
        if term_to_cancel == self.numerator:
            from ._theorems_ import frac_cancel_numer_left
            assert len(expr.denominator.operands) == 2, "Should be grouped"
            expr = eq.update(frac_cancel_numer_left.instantiate(
                {x: term_to_cancel, y: expr.denominator.operands[1]},
                assumptions=assumptions))
            return eq.relation
        elif term_to_cancel == self.denominator:
            from ._theorems_ import frac_cancel_denom_left
            assert len(expr.numerator.operands) == 2, "Should be grouped"
            expr = eq.update(frac_cancel_denom_left.instantiate(
                {x: term_to_cancel, y: expr.numerator.operands[1]},
                assumptions=assumptions))
            return eq.relation
        else:
            from ._theorems_ import frac_cancel_left
            expr = eq.update(frac_cancel_left.instantiate(
                {x: term_to_cancel, y: expr.numerator.operands[1],
                 z: expr.denominator.operands[1]},
                assumptions=assumptions))
            return eq.relation

    def deep_one_eliminations(self, assumptions=USE_DEFAULTS):
        '''
        Eliminate ones from the numerator, the denominator,
        and as a division by one.
        '''
        from proveit.numbers import one
        expr = self

        # A convenience to allow successive update to the equation
        # via transitivities (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        for _i, operand in enumerate(self.operands):
            if hasattr(operand, 'deep_one_eliminations'):
                expr = eq.update(expr.inner_expr().operands[_i].
                                 deep_one_eliminations(assumptions))

        if expr.denominator == one:
            expr = eq.update(expr.eliminate_divide_by_one(assumptions))
        return eq.relation

    def eliminate_divide_by_one(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import one
        from ._theorems_ import frac_one_denom
        if self.denominator != one:
            raise ValueError("'eliminate_divide_by_one' is only applicable "
                             "if the denominator is precisely one.")
        return frac_one_denom.instantiate({x: self.numerator},
                                          assumptions=assumptions)

    def distribution(self, assumptions=USE_DEFAULTS):
        r'''
        Distribute the denominator through the numerate.
        Returns the equality that equates self to this new version.
        Examples:
            :math:`(a + b + c) / d = a / d + b / d + c / d`
            :math:`(a - b) / d = a / d - b / d`
            :math:`\left(\sum_x f(x)\right / y = \sum_x [f(x) / y]`
        Give any assumptions necessary to prove that the operands are in the Complex
        numbers so that the associative and commutation theorems are applicable.
        '''
        from proveit.numbers import Add, subtract, Sum
        from ._theorems_ import distributefrac_through_sum, distributefrac_through_subtract, distributefrac_through_summation
        if isinstance(self.numerator, Add):
            return distributefrac_through_sum.instantiate(
                {x_etc: self.numerator.operands, y: self.denominator})
        elif isinstance(self.numerator, subtract):
            return distributefrac_through_subtract.instantiate(
                {x: self.numerator.operands[0], y: self.numerator.operands[1], z: self.denominator})
        elif isinstance(self.numerator, Sum):
            # Should deduce in Complex, but distribute_through_summation doesn't have a domain restriction right now
            # because this is a little tricky.   To do.
            #deduce_in_complex(self.operands, assumptions)
            y_etc_sub = self.numerator.indices
            Pop, Pop_sub = Operation(
                P, self.numerator.indices), self.numerator.summand
            S_sub = self.numerator.domain
            dummy_var = safe_dummy_var(self)
            spec1 = distributefrac_through_summation.instantiate(
                {Pop: Pop_sub, S: S_sub, y_etc: y_etc_sub, z: dummy_var})
            return spec1.derive_conclusion().instantiate(
                {dummy_var: self.denominator})
        else:
            raise Exception(
                "Unsupported operand type to distribute over: " +
                self.numerator.__class__)

    def exponent_combination(self, start_idx=None, end_idx=None,
                             assumptions=USE_DEFAULTS):
        '''
        Equates $a^m/a^n$ to $a^{m-n} or
        $a^c/b^c$ to $(a/b)^c$.
        '''
        from proveit.logic import InSet
        from proveit.numbers import (Exp, NaturalPos, RealPos, Real,
                                     Complex)
        from proveit.numbers.exponentiation._theorems_ import (
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
                    while len(possible_exponent_types) > 1:
                        exponent_type = possible_exponent_types[0]
                        if InSet(exponent, exponent_type).proven(assumptions):
                            # This type is known for this exponent.
                            break
                        # We've eliminated a type from being known.
                        possible_exponent_types.pop(0)
                known_exponent_type = possible_exponent_types[0]

                if known_exponent_type == NaturalPos:
                    _m, _n = exponents
                    return quotient_of_posnat_powers.instantiate(
                        {a: same_base, m: _m, n: _n}, assumptions=assumptions)
                else:
                    _b, _c = exponents
                    if known_exponent_type == RealPos:
                        thm = quotient_of_pos_powers
                    elif known_exponent_type == Real:
                        thm = quotient_of_real_powers
                    else:  # Complex is the default
                        thm = quotient_of_complex_powers
                    thm.instantiate({a: same_base, b: _b, c: _c},
                                    assumptions=assumptions)

            elif self.numerator.exponent == self.denominator.exponent:
                # Same exponent: (a^c/b^c) = (a/b)^c
                same_exponent = self.numerator.exponent
                bases = (self.numerator.base, self.denominator.base)
                # Combining the exponents in this case is the reverse
                # of disibuting an exponent.
                quotient = Div(*bases).with_matching_style(self)
                exp = Exp(quotient, same_exponent)
                return exp.distribution(
                    assumptions).derive_reversed(assumptions)
        else:
            raise NotImplementedError("Need to implement degenerate cases "
                                      "of a^b/a and a/a^b.")

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem.
        Created: 2/27/2020 by wdc, based on the same method in the Add
                 class. Just a start on this method, to be cont'd.
        Last Modified: 2/27/2020 by wdc. Creation.
        Once established, these authorship notations can be deleted.
        '''
        from proveit._common_ import a, b
        from proveit.numbers.division._theorems_ import (
            div_rational_closure, div_rational_non_zero_closure,
            div_rational_pos_closure, div_rational_non_neg_closure,
            div_real_closure, divide_real_pos_closure, divide_complex_closure)
        from proveit.numbers import (
            Rational, RationalNonZero, RationalPos, RationalNonNeg,
            Real, RealPos, Complex)

        thm = None
        if number_set == Rational:
            thm = div_rational_closure
        elif number_set == RationalNonZero:
            thm = div_rational_non_zero_closure
        elif number_set == RationalPos:
            thm = div_rational_pos_closure
        elif number_set == RationalNonNeg:
            thm = div_rational_non_neg_closure
        elif number_set == Real:
            thm = div_real_closure
        elif number_set == RealPos:
            thm = divide_real_pos_closure
        elif number_set == Complex:
            thm = divide_complex_closure
        if thm is not None:
            return thm.instantiate({a: self.numerator, b: self.denominator},
                                   assumptions=assumptions)

    """
    def factor(self,the_factor,pull="left", group_factor=False, group_remainder=None, assumptions=frozenset()):
        '''
        Pull out a factor from a fraction, pulling it either to the "left" or "right".
        The factor may be a product or fraction itself.
        If group_factor is True and the_factor is a product, it will be grouped together as a
        sub-product.  group_remainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in the Complex numbers so that
        the associative and commutation theorems are applicable.
        '''
        from ._theorems_ import frac_in_prod_rev, prod_of_fracs_rev, prod_of_fracs_left_numer_one_rev, prod_of_fracs_right_numer_one_rev
        from proveit.numbers import Mult, num
        dummy_var = safe_dummy_var(self)
        eqns = []
        if isinstance(the_factor, frac):
            # factor the operand denominator out of self's denominator
            denom_factor_eqn = self.denominator.factor(the_factor.denominator, pull, group_factor=True, group_remainder=True, assumptions=assumptions)
            factored_denom = denom_factor_eqn.rhs
            eqns.append(denom_factor_eqn.substitution(frac(self.numerator, dummy_var), dummy_var))
            if the_factor.numerator != num(1) and self.numerator != num(1):
                # factor the operand numerator out of self's numerator
                numer_factor_eqn = self.numerator.factor(the_factor.numerator, pull, group_factor=True, group_remainder=True, assumptions=assumptions)
                factored_numer = numer_factor_eqn.rhs
                eqns.append(numer_factor_eqn.substitution(frac(dummy_var, factored_denom), dummy_var))
                # factor the two fractions
                eqns.append(prod_of_fracs_rev.instantiate({x:factored_numer.operands[0], y:factored_numer.operands[1],
                                                    z:factored_denom.operands[0], w:factored_denom.operands[1]}))
            else:
                # special case: one of the numerators is equal to one, no numerator factoring to be done
                if (pull == 'left') == (the_factor.numerator == num(1)):
                    thm = prod_of_fracs_left_numer_one_rev
                else:
                    thm = prod_of_fracs_right_numer_one_rev
                # factor the two fractions
                eqns.append(thm.instantiate({x:self.numerator, y:factored_denom.operands[0], z:factored_denom.operands[1]}))
        else:
            numer_factor_eqn = self.numerator.factor(the_factor, pull, group_factor=False, group_remainder=True, assumptions=assumptions)
            factored_numer = numer_factor_eqn.rhs
            eqns.append(numer_factor_eqn.substitution(frac(dummy_var, self.denominator), dummy_var))
            # factor the numerator factor from the fraction
            if pull == 'left':
                w_etc_sub = factored_numer.operands[:-1]
                x_sub = factored_numer.operands[-1]
                z_etc_sub = []
            elif pull == 'right':
                w_etc_sub = []
                x_sub = factored_numer.operands[0]
                z_etc_sub = factored_numer.operands[1:]
            eqns.append(frac_in_prod_rev.instantiate({w_etc:w_etc_sub, x:x_sub, y:self.denominator, z_etc:z_etc_sub}))
            num = len(the_factor.operands) if isinstance(the_factor, Mult) else 1
            if group_factor and num > 1:
                if pull=='left':
                    eqns.append(eqns[-1].rhs.group(end_idx=num, assumptions=assumptions))
                elif pull=='right':
                    eqns.append(eqns[-1].rhs.group(start_idx=-num, assumptions=assumptions))
        return Equals(eqns[0].lhs, eqns[-1].rhs).prove(assumptions)
    """


def frac(numer, denom):
    return Div(numer, denom).with_styles(division='fraction')


# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(
    Div,
    'deep_one_eliminations',
    'deep_eliminated_ones',
    'deep_eliminate_ones')
InnerExpr.register_equivalence_method(
    Div,
    'exponent_combination',
    'combined_exponents',
    'combine_exponents')
