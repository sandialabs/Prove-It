from proveit import (Judgment, Expression, Literal, Operation,
                     maybe_fenced_latex, defaults,
                     Function, ExprTuple, InnerExpr, USE_DEFAULTS,
                     UnsatisfiedPrerequisites, relation_prover,
                     equality_prover)
from proveit import TransRelUpdater
from proveit import a, b, c, m, n, w, x, y, z
from proveit.numbers import NumberOperation

class Div(NumberOperation):
    # operator of the Add operation
    _operator_ = Literal(
        string_format='/',
        latex_format=r'\div',
        theory=__file__)

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

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Divide
        expression assuming the operands have been simplified.

        Specifically, cancels common factors and eliminates ones.
        '''
        from proveit.logic import is_irreducible_value
        from proveit.numbers import one
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)

        # perform cancelations where possible
        expr = eq.update(expr.cancelations(preserve_all=True))
        if not isinstance(expr, Div):
            # complete cancelation.
            return eq.relation

        if must_evaluate and not all(
                is_irreducible_value(operand) for operand in self.operands):
            for operand in self.operands:
                if not is_irreducible_value(operand):
                    # The simplification of the operands may not have
                    # worked hard enough.  Let's work harder if we
                    # must evaluate.            
                    operand.evalution()
            return self.evaluation()

        if expr.denominator == one:
            # eliminate division by one
            eq.update(expr.divide_by_one_elimination(auto_simplify=False))
            return eq.relation  # no more division simplifications.

        return eq.relation

    """
    # outdated.  obsolete.
    def combine_exponents(self, assumptions=USE_DEFAULTS):
        from . import frac_int_exp, frac_nat_pos_exp
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
            if (not isinstance(self.numerator, Mult) or
                    term_to_cancel not in self.numerator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 % (term_to_cancel, self))
            # Factor the term_to_cancel from the numerator to the left.
            expr = eq.update(expr.inner_expr().numerator.factorization(
                term_to_cancel, group_factor=True, group_remainder=True,
                preserve_all=True))
        if term_to_cancel != self.denominator:
            if (not isinstance(self.denominator, Mult) or
                    term_to_cancel not in self.denominator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 % (term_to_cancel, self))
            # Factor the term_to_cancel from the denominator to the left.
            expr = eq.update(expr.inner_expr().denominator.factorization(
                term_to_cancel, group_factor=True, group_remainder=True,
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
    def factorization(self, the_factor, pull="left",
                      group_factor=True, group_remainder=True,
                      **defaults_config):
        '''
        Return the proven factorization (equality with the factored
        form) from pulling "the_factor" from this division to the "left"
        or "right".  If there are multiple occurrences, the first
        occurrence is used.  If group_factor is True and the_factor is
        a product, these operands are grouped together as a sub-product.
        If group_remainder is True and there are multiple remaining
        operands (those not in "the_factor"), then these remaining
        operands are grouped together as a sub-product.
        The group_remainder parameter is not relevant but kept
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
        if the_factor == self:
            return eq.relation # self = self
        if isinstance(the_factor, Div):
            the_factor_numer = the_factor.numerator
            the_factor_denom = the_factor.denominator
        else:
            the_factor_numer = the_factor
            the_factor_denom = one
        replacements = []
        # Factor out a fraction.
        if expr.denominator == the_factor_denom:
            # Factor (x/z) from (x*y)/z.
            # x or y may be 1.
            if the_factor_numer not in (one, expr.numerator):
                expr = eq.update(expr.inner_expr().numerator.factorization(
                        the_factor.numerator, pull=pull,
                        group_factor=True, group_remainder=True))
            if pull == 'left':
                # factor (x*y)/z into (x/z)*y
                thm = mult_frac_left
                if the_factor_numer == one:
                    # factor y/z into (1/z)*y
                    _x = one
                    _y = expr.numerator
                    replacements.append(Mult(_x, _y).one_elimination(0))
            else:
                # factor (x*y)/z into x*(y/z)
                thm = mult_frac_right
                if the_factor_numer == one:
                    # factor x/z into x*(1/z)
                    _x = expr.numerator
                    _y = one
                    replacements.append(Mult(_x, _y).one_elimination(1))
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
                        group_factor=True))
                assert expr.denominator.operands.num_entries() == 2
                _z = expr.denominator.operands.entries[0]
                _w = expr.denominator.operands.entries[1]
            elif (pull == 'left') == (the_factor_denom == one):
                # Factor (x*y)/w into x*(y/w).
                _z = one
                _w = expr.denominator
                replacements.append(Mult(_z, _w).one_elimination(0))
            else:
                # Factor (x*y)/z into (x/z)*y.
                _z = expr.denominator
                _w = one
                replacements.append(Mult(_z, _w).one_elimination(1))
            # Factor the numerator parts unless there is a 1 numerator.
            if the_factor_numer not in (one, expr.numerator):
                expr = eq.update(expr.inner_expr().numerator.factorization(
                        the_factor_numer, pull=pull,
                        group_factor=True, group_remainder=True))
                assert expr.numerator.operands.num_entries() == 2
                # Factor (x*y)/(z*w) into (x/z)*(y/w)
                _x = expr.numerator.operands.entries[0]
                _y = expr.numerator.operands.entries[1]
            elif (pull == 'left') == (the_factor_numer == one):
                # Factor y/(z*w) into (1/z)*(y/w)
                _x = one
                _y = expr.numerator
                replacements.append(Mult(_x, _y).one_elimination(0))
            else:
                # Factor x/(y*z) into (x/y)*(1/z)
                _x = expr.numerator
                _y = one
                replacements.append(Mult(_x, _y).one_elimination(1))
            # create POSSIBLE replacements for inadvertently generated
            # fractions of the form _x/1 (i.e. _z = 1)
            # or _y/1 (i.e. _w = 1):
            if _z == one:
                replacements.append(frac(_x, _z).divide_by_one_elimination())
            if _w == one:
                replacements.append(frac(_y, _w).divide_by_one_elimination())

            temp_expr = eq.update(thm.instantiate({x:_x, y:_y, z:_z, w:_w},
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

    @equality_prover('combined_exponents', 'combine_exponents')
    def exponent_combination(self, start_idx=None, end_idx=None,
                             **defaults_config):
        '''
        Equates $a^m/a^n$ to $a^{m-n} or
        $a^c/b^c$ to $(a/b)^c$.
        '''
        from proveit.logic import InSet
        from proveit.numbers import (Exp, NaturalPos, RealPos, Real,
                                     Complex)
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
        from proveit.numbers.division import (
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
            return thm.instantiate({a: self.numerator, b: self.denominator})
        raise NotImplementedError(
            "'Div.deduce_in_number_set()' not implemented for the %s set"
            % str(number_set))

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        Deduce a bound of this division (fraction) given a bound on
        either the numerator or the denominatory.
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
