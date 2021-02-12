from proveit import (Literal, Function, ExprTuple, InnerExpr, ProofFailure,
                     maybe_fenced_string, USE_DEFAULTS, StyleOptions)
from proveit.logic import Membership
import proveit
from proveit import a, b, c, k, m, n, x, S
from proveit.numbers import one, two, Div, frac, num


class Exp(Function):
    '''
    An Expression class to represent an exponentiation.  Derive from
    Function since infix notation should not be a style option.
    '''
    # operator of the Exp operation.
    _operator_ = Literal(string_format='Exp', theory=__file__)

    def __init__(self, base, exponent):
        r'''
        Raise base to exponent power.
        '''
        self.base = base
        self.exponent = exponent
        Function.__init__(self, Exp._operator_, (base, exponent))
    
    def remake_constructor(self):
        if self.get_style('exponent') == 'radical':
            # Use a different constructor if using the 'radical' style.
            if self.exponent == frac(one, two):
                return 'sqrt'
            else:
                raise ValueError(
                    "Unkown radical type, exponentiating to the power "
                    "of %s" % str(
                        self.exponent))
        return Function.remake_constructor(self)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        if self.get_style('exponent') == 'radical':
            yield self.base
        else:
            yield self.base
            yield self.exponent

    def membership_object(self, element):
        return ExpSetMembership(element, self)
    
    def style_options(self):
        '''
        Returns the StyleOptions object for this Exp.
        '''
        options = StyleOptions(self)
        default_exp_style = ('radical' if self.exponent==frac(one, two)
                             else 'raised')
        options.add_option(
                name = 'exponent',
                description = ("'raised': exponent as a superscript; "
                               "'radical': using a radical sign"),
                default = default_exp_style,
                related_methods = ('with_radical', 'without_radical'))
        return options
        
    def with_radical(self):
        return self.with_styles(exponent='radical')

    def without_radical(self):
        return self.with_styles(exponent='raised')

    def _closureTheorem(self, number_set):
        import natural.theorems
        import real.theorems
        import complex.theorems
        from proveit.numbers import two
        if number_set == NaturalPos:
            return natural.theorems.pow_closure
        elif number_set == Real:
            return real.theorems.pow_closure
        elif number_set == RealPos:
            if self.exponent != two:  # otherwise, use
                # deduce_in_real_pos_directly(..)
                return real.theorems.pow_pos_closure
        elif number_set == Complex:
            return complex.theorems.pow_closure

    def do_reduced_simplification(self, assumptions=USE_DEFAULTS):
        '''
        For trivial cases, a zero or one exponent or zero or one base,
        derive and return this exponential expression equated with a
        simplified form. Assumptions may be necessary to deduce
        necessary conditions for the simplification.
        '''
        from proveit.logic import Equals, InSet
        from proveit.numbers import one, two, Rational, Real, Abs
        from proveit.relation import TransRelUpdater
        from . import complex_x_to_first_power_is_x
        if self.exponent == one:
            return complex_x_to_first_power_is_x.instantiate({a: self.base})
        if (isinstance(self.base, Exp) and
            isinstance(self.base.exponent, Div) and
            self.base.exponent.numerator == one and
                self.base.exponent.denominator == self.exponent):
            from . import nth_power_of_nth_root
            _n, _x = nth_power_of_nth_root.instance_params
            return nth_power_of_nth_root.instantiate(
                {_n: self.exponent, _x: self.base.base}, assumptions=assumptions)

        expr = self
        # for convenience updating our equation:
        eq = TransRelUpdater(expr, assumptions)
        if self.exponent == two and isinstance(self.base, Abs):
            from . import (square_abs_rational_simp,
                                     square_abs_real_simp)
            # |a|^2 = a if a is real
            rational_base = InSet(self.base, Rational).proven(assumptions)
            real_base = InSet(self.base, Real).proven(assumptions)
            thm = None
            if rational_base:
                thm = square_abs_rational_simp
            elif real_base:
                thm = square_abs_real_simp
            if thm is not None:
                simp = thm.instantiate({a: self.base.operand},
                                       assumptions=assumptions)
                expr = eq.update(simp)
                # A further simplification may be possible after
                # eliminating the absolute value.
                expr = eq.update(expr.simplification(assumptions))

        return eq.relation

    def do_reduced_evaluation(self, assumptions=USE_DEFAULTS):
        '''
        For trivial cases, a zero or one exponent or zero or one base,
        derive and return this exponential expression equated with a
        evaluated form. Assumptions may be necessary to deduce
        necessary conditions for the simplification.
        '''
        from proveit.logic import EvaluationError
        from proveit.numbers import zero, one
        from . import exp_zero_eq_one, exponentiated_zero, exponentiated_one
        if self.exponent == zero:
            return exp_zero_eq_one.instantiate({a: self.base})  # =1
        elif self.base == zero:
            return exponentiated_zero.instantiate({x: self.exponent})  # =0
        elif self.base == one:
            return exponentiated_one.instantiate({x: self.exponent})  # =1
        else:
            raise EvaluationError('Only trivial evaluation is implemented '
                                  '(zero or one for the base or exponent).',
                                  assumptions)
    
    def not_equal(self, other, assumptions=USE_DEFAULTS):
        '''
        Attempt to prove that self is not equal to other.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers import zero
        if other == zero:
            return self.deduce_not_zero(assumptions)
        # If it isn't a special case treated here, just use
        # conclude-as-folded.
        return NotEquals(self, other).conclude_as_folded(assumptions)
    
    def deduce_not_zero(self, assumptions=USE_DEFAULTS):
        '''
        Prove that this exponential is not zero given that
        the base is not zero.
        '''
        from proveit.logic import InSet
        from proveit.numbers import RationalPos
        from . import exp_rational_non_zero__not_zero, exp_not_eq_zero
        if (not exp_not_eq_zero.is_usable() or (
                InSet(self.base, RationalPos).proven(assumptions) and
                InSet(self.exponent, RationalPos).proven(assumptions))):
            # Special case where the base and exponent are RationalPos.
            return exp_rational_non_zero__not_zero.instantiate(
                {a: self.base, b: self.exponent}, assumptions=assumptions)
        return exp_not_eq_zero.instantiate(
            {a: self.base, b: self.exponent}, assumptions=assumptions)

    def deduce_in_real_pos_directly(self, assumptions=frozenset()):
        import real.theorems
        from number import two
        if self.exponent == two:
            deduce_in_real(self.base, assumptions)
            deduce_not_zero(self.base, assumptions)
            return real.theorems.sqrd_closure.instantiate(
                {a: self.base}).checked(assumptions)
        # only treating certain special case(s) in this manner
        raise DeduceInNumberSetException(self, RealPos, assumptions)

    def expansion(self, assumptions=USE_DEFAULTS):
        '''
        From self of the form x^n return x^n = x(x)...(x).
        For example, Exp(x, two).expansion(assumptions)
        should return: assumptions |- (x^2) =  (x)(x). Currently only
        implemented explicitly for powers of n=2 and n=3.
        '''
        exponent = self.exponent
        if exponent == num(2):
            from . import square_expansion
            _x = square_expansion.instance_param
            return square_expansion.instantiate(
                {_x: self.base}, assumptions=assumptions)

        if exponent == 3:
            from . import cube_expansion
            _x = cube_expansion.instance_param
            return cube_expansion.instantiate(
                {_x: self.base}, assumptions=assumptions)

        raise ValueError("Exp.expansion() implemented only for exponential "
                         "powers n=2 or n=3, but received an exponential "
                         "power of {0}.".format(exponent))

    def _not_eqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.pow_not_eq_zero

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, **kwargs):
        # begin building the inner_str
        inner_str = self.base.formatted(
            format_type, fence=True, force_fence=True)
        if self.get_style('exponent') == 'raised':
            inner_str = (
                inner_str
                + r'^{' + self.exponent.formatted(format_type, fence=False)
                + '}')
        elif self.get_style('exponent') == 'radical':
            if self.exponent == frac(one, two):
                if format_type == 'string':
                    inner_str = (
                        r'sqrt('
                        + self.base.formatted(format_type, fence=True,
                                              force_fence=True)
                        + ')')
                elif format_type == 'latex':
                    inner_str = (
                        r'\sqrt{'
                        + self.base.formatted(format_type, fence=True,
                                              force_fence=True)
                        + '}')
            else:
                raise ValueError(
                    "Unkown radical type, exponentiating to the power "
                    "of %s" % str(
                        self.exponent))

        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def distribution(self, assumptions=USE_DEFAULTS):
        '''
        Equate this exponential to a form in which the exponent
        is distributed over factors, or a power of a power reduces to
        a power of multiplied exponents.
        Examples:
            (a*b*c)^f = a^f * b^f * c^f
            (a/b)^f = (a^f / b^f)
            (a^b)^c = a^(b*c)
        '''
        from proveit.logic import InSet
        from proveit.numbers import Mult, Div, NaturalPos, RealPos, Real
        from . import (
            posnat_power_of_product, posnat_power_of_products,
            posnat_power_of_quotient, posnat_power_of_posnat_power,
            pos_power_of_product, pos_power_of_products,
            pos_power_of_quotient, pos_power_of_pos_power,
            real_power_of_product, real_power_of_products,
            real_power_of_quotient, real_power_of_real_power,
            complex_power_of_product, complex_power_of_products,
            complex_power_of_quotient, complex_power_of_complex_power)
        base = self.base
        exponent = self.exponent
        if isinstance(base, Mult):
            if self.base.operands.is_double():
                _a, _b = self.base.operands
            else:
                _m = self.operands.num_elements(assumptions)
                _a = self.operands
            if InSet(exponent, NaturalPos).proven(assumptions):
                if self.base.operands.is_double():
                    return posnat_power_of_product.instantiate(
                        {a: _a, b: _b, n: exponent}, assumptions=assumptions)
                else:
                    return posnat_power_of_products.instantiate(
                        {m: _m, a: _a, n: exponent}, assumptions=assumptions)
            elif InSet(exponent, RealPos).proven(assumptions):
                if self.base.operands.is_double():
                    return pos_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent}, assumptions=assumptions)
                else:
                    return pos_power_of_products.instantiate(
                        {m: _m, a: _a, c: exponent}, assumptions=assumptions)
            elif InSet(exponent, Real).proven(assumptions):
                if self.base.operands.is_double():
                    return real_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent}, assumptions=assumptions)
                else:
                    return real_power_of_products.instantiate(
                        {m: _m, a: _a, c: exponent}, assumptions=assumptions)
            else:  # Complex is the default
                if self.base.operands.is_double():
                    return complex_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent}, assumptions=assumptions)
                else:
                    return complex_power_of_products.instantiate(
                        {m: _m, a: _a, c: exponent}, assumptions=assumptions)
        elif isinstance(base, Div):
            assert self.base.operands.is_double()
            _a, _b = self.base.operands
            if InSet(exponent, NaturalPos).proven(assumptions):
                return posnat_power_of_quotient.instantiate(
                    {a: _a, b: _b, n: exponent}, assumptions=assumptions)
            else:
                if InSet(exponent, RealPos).proven(assumptions):
                    thm = pos_power_of_quotient
                elif InSet(exponent, Real).proven(assumptions):
                    thm = real_power_of_quotient
                else:  # Complex is the default
                    thm = complex_power_of_quotient
                return thm.instantiate(
                    {a: _a, b: _b, c: exponent}, assumptions=assumptions)
        elif isinstance(base, Exp):
            _a = base.base
            if InSet(exponent, NaturalPos).proven(assumptions):
                _m, _n = base.exponent, exponent
                return posnat_power_of_posnat_power.instantiate(
                    {a: _a, m: _m, n: _n}, assumptions=assumptions)
            else:
                _b, _c = base.exponent, exponent
                if InSet(exponent, RealPos).proven(assumptions):
                    thm = pos_power_of_pos_power
                elif InSet(exponent, Real).proven(assumptions):
                    thm = real_power_of_real_power
                else:  # Complex is the default
                    thm = complex_power_of_complex_power
                return thm.instantiate(
                    {a: _a, b: _b, c: _c}, assumptions=assumptions)
        else:
            raise ValueError("May only distribute an exponent over a "
                             "product or fraction.")

    """
    def distribute_exponent(self, assumptions=frozenset()):
        from proveit.numbers import Div
        from proveit.numbers.division.theorems import (
                frac_int_exp_rev, frac_nat_pos_exp_rev)
        if isinstance(self.base, Div):
            exponent = self.exponent
            try:
                deduce_in_natural_pos(exponent, assumptions)
                deduce_in_complex([self.base.numerator, self.base.denominator],
                                  assumptions)
                deduce_not_zero(self.base.denominator, assumptions)
                return frac_nat_pos_exp_rev.instantiate(
                        {n:exponent}).instantiate(
                            {a:self.numerator.base, b:self.denominator.base})
            except:
                deduce_in_integer(exponent, assumptions)
                deduce_in_complex([self.base.numerator, self.base.denominator],
                                  assumptions)
                deduce_not_zero(self.base.numerator, assumptions)
                deduce_not_zero(self.base.denominator, assumptions)
                return frac_int_exp_rev.instantiate(
                        {n:exponent}).instantiate(
                            {a:self.base.numerator, b:self.base.denominator})
        raise Exception('distribute_exponent currently only implemented for a '
                        'fraction base')
    """

    def raise_exp_factor(self, exp_factor, assumptions=USE_DEFAULTS):
        # Note: this is out-of-date.  Distribution handles this now,
        # except it doesn't deal with the negation part
        # (do we need it to?)
        from proveit.numbers import Neg
        from .theorems import int_exp_of_exp, int_exp_of_neg_exp
        if isinstance(self.exponent, Neg):
            b_times_c = self.exponent.operand
            thm = int_exp_of_neg_exp
        else:
            b_times_c = self.exponent
            thm = int_exp_of_exp
        if not hasattr(b_times_c, 'factor'):
            raise ValueError('Exponent not factorable, may not raise the '
                             'exponent factor.')
        factor_eq = b_times_c.factor(exp_factor, pull='right',
                                     group_remainder=True,
                                     assumptions=assumptions)
        if factor_eq.lhs != factor_eq.rhs:
            # factor the exponent first, then raise this exponent factor
            factored_exp_eq = factor_eq.substitution(self)
            return factored_exp_eq.apply_transitivity(
                factored_exp_eq.rhs.raise_exp_factor(exp_factor,
                                                     assumptions=assumptions))
        n_sub = b_times_c.operands[1]
        a_sub = self.base
        b_sub = b_times_c.operands[0]
        deduce_not_zero(a_sub, assumptions)
        deduce_in_integer(n_sub, assumptions)
        deduce_in_complex([a_sub, b_sub], assumptions)
        return thm.instantiate({n: n_sub}).instantiate(
            {a: a_sub, b: b_sub}).derive_reversed()

    def lower_outer_exp(self, assumptions=frozenset()):
        #
        from proveit.numbers import Neg
        from .theorems import (
            int_exp_of_exp,
            int_exp_of_neg_exp,
            neg_int_exp_of_exp,
            neg_int_exp_of_neg_exp)
        if not isinstance(self.base, Exp):
            raise Exception('May only apply lower_outer_exp to nested '
                            'Exp operations')
        if isinstance(
                self.base.exponent,
                Neg) and isinstance(
                self.exponent,
                Neg):
            b_, n_ = self.base.exponent.operand, self.exponent.operand
            thm = neg_int_exp_of_neg_exp
        elif isinstance(self.base.exponent, Neg):
            b_, n_ = self.base.exponent.operand, self.exponent
            thm = int_exp_of_neg_exp
        elif isinstance(self.exponent, Neg):
            b_, n_ = self.base.exponent, self.exponent.operand
            thm = neg_int_exp_of_exp
        else:
            b_, n_ = self.base.exponent, self.exponent
            thm = int_exp_of_exp
        a_ = self.base.base
        deduce_not_zero(self.base.base, assumptions)
        deduce_in_integer(n_, assumptions)
        deduce_in_complex([a_, b_], assumptions)
        return thm.instantiate({n: n_}).instantiate({a: a_, b: b_})

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem. This method uses instantiated thms for the sqrt() cases.
        Created: 2/20/2020 by wdc, based on the same method in the Add
                 class.
        Last modified: 2/28/2020 by wdc. Added instantiation for
                       sqrt() cases created using the sqrt() fxn.
        Last Modified: 2/20/2020 by wdc. Creation.
        Once established, these authorship notations can be deleted.
        '''
        from proveit.logic import InSet, NotEquals
        from proveit.numbers.exponentiation import (
            exp_complex_closure, exp_natpos_closure,
            exp_nat_closure, exp_int_closure, 
            exp_rational_closure_natpos_power, exp_rational_closure_int_power,
            exp_rational_closure, exp_real_closure,
            exp_real_closure_nonneg_base, exp_real_closure_base_pos,
            exp_real_closure_natpos_power, exp_real_pos_closure,
            sqrt_complex_closure, sqrt_real_closure,
            sqrt_real_pos_closure)
        from proveit.numbers import (
            Natural, NaturalPos, Integer, Rational, 
            Real, RealPos, RealNonNeg, Complex)
        from proveit.numbers import zero

        if number_set == NaturalPos:
            return exp_natpos_closure.instantiate(
                {a: self.base, b: self.exponent}, assumptions=assumptions)
        elif number_set == Natural:
            return exp_nat_closure.instantiate(
                {a: self.base, b: self.exponent}, assumptions=assumptions)
        elif number_set == Integer:
            return exp_int_closure.instantiate(
                {a: self.base, b: self.exponent}, assumptions=assumptions)
        elif number_set == Rational:
            power_is_nonpos = InSet(self.exponent, NaturalPos)
            if power_is_nonpos.proven(assumptions):
                thm = exp_rational_closure_natpos_power
            elif NotEquals(self.base, zero):
                thm = exp_rational_closure_int_power
            else:
                thm = exp_rational_closure # catch-all theorem
            return thm.instantiate(
                    {a: self.base}, assumptions=assumptions)
        elif number_set == Real:
            # Would prefer the more general approach commented-out
            # above; in the meantime, allowing for 2 possibilities here:
            # if base is positive real, exp can be any real;
            # if base is real ≥ 0, exp must be non-zero
            if self.exponent == frac(one, two):
                return sqrt_real_closure.instantiate(
                    {a: self.base}, assumptions=assumptions)
            else:
                power_is_nonpos = InSet(self.exponent, NaturalPos)
                if power_is_nonpos.proven(assumptions):
                    thm = exp_real_closure_natpos_power
                elif InSet(self.base, RealPos).proven(assumptions):
                    thm = exp_real_closure_base_pos
                elif InSet(self.base, RealNonNeg).proven(assumptions):
                    thm = exp_real_closure_nonneg_base
                else:
                    thm = exp_real_closure # catch-all theorem
                return thm.instantiate(
                        {a: self.base, b: self.exponent},
                        assumptions=assumptions)
        elif number_set == RealPos:
            if self.exponent == frac(one, two):
                return sqrt_real_pos_closure.instantiate(
                    {a: self.base}, assumptions=assumptions)
            else:
                return exp_real_pos_closure.instantiate(
                    {a: self.base, b: self.exponent}, assumptions=assumptions)
        elif number_set == Complex:
            if self.exponent == frac(one, two):
                return sqrt_complex_closure.instantiate(
                    {a: self.base}, assumptions=assumptions)
            else:
                return exp_complex_closure.instantiate(
                    {a: self.base, b: self.exponent},
                    assumptions=assumptions)

        msg = ("'Exp.deduce_in_number_set' not implemented for the %s set" 
              % str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)


class ExpSetMembership(Membership):
    '''
    Defines methods that apply to membership in an exponentiated set.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude that the element is in the exponentiated set.
        '''
        from proveit.logic import InSet
        from proveit.logic.sets.membership import (
            exp_set_0, exp_set_1, exp_set_2, exp_set_3, exp_set_4, exp_set_5,
            exp_set_6, exp_set_7, exp_set_8, exp_set_9)
        from proveit.numbers import zero, is_literal_int, DIGITS
        element = self.element
        domain = self.domain
        elem_in_set = InSet(element, domain)
        if not isinstance(element, ExprTuple):
            raise ProofFailure(
                elem_in_set, assumptions,
                "Can only automatically deduce membership in exponentiated "
                "sets for an element that is a list")
        exponent_eval = domain.exponent.evaluation(assumptions=assumptions)
        exponent = exponent_eval.rhs
        base = domain.base
        #print(exponent, base, exponent.as_int(),element, domain, len(element))
        if is_literal_int(exponent):
            if exponent == zero:
                return exp_set_0.instantiate(
                    {S: base}, assumptions=assumptions)
            if element.num_entries() != exponent.as_int():
                raise ProofFailure(
                    elem_in_set, assumptions,
                    "Element not a member of the exponentiated set; "
                    "incorrect list length")
            elif exponent in DIGITS:
                # thm = forall_S forall_{a, b... in S} (a, b, ...) in S^n
                thm = locals()['exp_set_%d' % exponent.as_int()]
                expr_map = {S: base}  # S is the base
                # map a, b, ... to the elements of element.
                expr_map.update({proveit.__getattr__(
                    chr(ord('a') + k)): elem_k for k, elem_k in enumerate(element)})
                elem_in_set = thm.instantiate(
                    expr_map, assumptions=assumptions)
            else:
                raise ProofFailure(
                    elem_in_set, assumptions,
                    "Automatic deduction of membership in exponentiated sets "
                    "is not supported beyond an exponent of 9")
        else:
            raise ProofFailure(
                elem_in_set, assumptions,
                "Automatic deduction of membership in exponentiated sets is "
                "only supported for an exponent that is a literal integer")
        if exponent_eval.lhs != exponent_eval.rhs:
            # after proving that the element is in the set taken to
            # the evaluation of the exponent, substitute back in the
            # original exponent.
            return exponent_eval.sub_left_side_into(elem_in_set,
                                                    assumptions=assumptions)
        return elem_in_set

    def side_effects(self, judgment):
        return
        yield

# outside any specific class:
# special Exp case of square root


def sqrt(base):
    '''
    Special function for square root version of an exponential.
    '''
    return Exp(base, frac(one, two))

def sqrd(base):
    '''
    Special function for squaring root version of an exponential.
    '''
    return Exp(base, two)


# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(
    Exp, 'distribution', 'distributed', 'distribute')
