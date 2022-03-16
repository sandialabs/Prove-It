from proveit import (defaults, equality_prover, ExprTuple, Function,
                     InnerExpr, Literal, maybe_fenced_string,
                     ProofFailure, prover, relation_prover, StyleOptions,
                     UnsatisfiedPrerequisites, USE_DEFAULTS)
import proveit
from proveit import a, b, c, k, m, n, x, y, S
from proveit import (defaults, Literal, Function, ExprTuple, InnerExpr,
                     ProofFailure, maybe_fenced_string, USE_DEFAULTS,
                     StyleOptions)
from proveit.logic import Equals, InSet, SetMembership, NotEquals
from proveit.numbers import zero, one, two, Div, frac, num, Real
from proveit.numbers import Integer, NumberOperation, deduce_number_set
from proveit.numbers.number_sets import (
    Natural, NaturalPos,
    Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
    Rational, RationalNonZero, RationalPos, RationalNeg, RationalNonNeg,
    RationalNonPos,
    Real, RealNonZero, RealNeg, RealPos, RealNonNeg, RealNonPos,
    Complex, ComplexNonZero)

class Exp(NumberOperation):
    '''
    An Expression class to represent an exponentiation.  Derive from
    Function since infix notation should not be a style option.
    '''
    # operator of the Exp operation.
    _operator_ = Literal(string_format='Exp', theory=__file__)

    def __init__(self, base, exponent, *, styles=None):
        r'''
        Raise base to exponent power.
        '''
        self.base = base
        self.exponent = exponent
        NumberOperation.__init__(self, Exp._operator_, (base, exponent),
                                 styles=styles)

    def remake_constructor(self):
        if (self.get_style('exponent', 'raised') == 'radical' and
                self.exponent == frac(one, two)):
            return 'sqrt'
        return Function.remake_constructor(self)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        if (self.get_style('exponent', 'raised') == 'radical' and
                self.exponent == frac(one, two)):
            yield self.base
        else:
            yield self.base
            yield self.exponent

    def style_options(self):
        '''
        Returns the StyleOptions object for this Exp.
        '''
        options = StyleOptions(self)
        if (isinstance(self.exponent, Div) and
                self.exponent.numerator == one):
            options.add_option(
                name='exponent',
                description=("'raised': exponent as a superscript; "
                             "'radical': using a radical sign"),
                default='radical',
                related_methods=('with_radical', 'without_radical'))
        return options

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, **kwargs):
        # begin building the inner_str
        inner_str = self.base.formatted(
            format_type, fence=True, force_fence=True)
        # if self.get_style('exponent', 'TEST') == 'TEST' and self.exponent == frac(one, two):
        #     self.with_radical()
        if self.get_style('exponent', 'raised') == 'raised':
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
            elif isinstance(self.exponent, Div):
                if format_type == 'string':
                    inner_str = (
                            self.exponent.denominator.formatted(format_type, fence=False)
                            + r' radical('
                            + self.base.formatted(format_type, fence=True,
                                                  force_fence=True)
                            + ')')
                elif format_type == 'latex':
                    inner_str = (
                            r'\sqrt[\leftroot{-3}\uproot{3}'
                            + self.exponent.denominator.formatted(format_type, fence=False) + ']{'
                            + self.base.formatted(format_type, fence=True,
                                                  force_fence=True)
                            + '}')
            else:
                raise ValueError(
                    "Unknown radical type, exponentiating to the power "
                    "of %s" % str(
                        self.exponent))

        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def membership_object(self, element):
        return ExpSetMembership(element, self)

    def with_radical(self):
        return self.with_styles(exponent='radical')

    def without_radical(self):
        return self.with_styles(exponent='raised')

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Exp
        expression assuming the operands have been simplified.

        Handles the following evaluations:
            a^0 = 1 for any complex a
            0^x = 0 for any positive x
            1^x = 1 for any complex x
            a^(Log(a, x)) = x for RealPos a and x, a != 1.
            x^n = x*x*...*x = ? for a natural n and irreducible x.

        Handles a zero or one exponent or zero or one base as
        simplifications.
        '''
        from proveit.relation import TransRelUpdater
        from proveit.logic import EvaluationError, is_irreducible_value
        from proveit.logic import InSet
        from proveit.numbers import (zero, one, two, is_literal_int,
                                     Log, Rational, Abs)
        from . import (exp_zero_eq_one, exponentiated_zero,
                       exponentiated_one, exp_nat_pos_expansion)

        if self.exponent == zero:
            return exp_zero_eq_one.instantiate({a: self.base})  # =1
        elif self.base == zero:
            # Will fail if the exponent is not positive, but this
            # is the only sensible thing to try.
            return exponentiated_zero.instantiate({x: self.exponent})  # =0
        elif self.base == one:
            return exponentiated_one.instantiate({x: self.exponent})  # =1
        elif (is_irreducible_value(self.base) and
                  is_literal_int(self.exponent) and
                  self.exponent.as_int() > 1):
            expr = self
            eq = TransRelUpdater(expr)
            expr = eq.update(exp_nat_pos_expansion.instantiate(
                    {x:self.base, n:self.exponent}, preserve_all=True))
            # We should come up with a better way of reducing
            # ExprRanges representing repetitions:
            _n = self.exponent.as_int()
            if _n <= 0 or _n > 9:
                raise NotImplementedError("Currently only implemented for 1-9")
            repetition_thm = proveit.numbers.numerals.decimals \
                .__getattr__('reduce_%s_repeats' % _n)
            rep_reduction = repetition_thm.instantiate({x: self.base})
            expr = eq.update(expr.inner_expr().operands.substitution(
                    rep_reduction.rhs, preserve_all=True))
            expr = eq.update(expr.evaluation())
            return eq.relation
        elif must_evaluate:
            if not all(is_irreducible_value(operand) for
                       operand in self.operands):
                for operand in self.operands:
                    if not is_irreducible_value(operand):
                        # The simplification of the operands may not have
                        # worked hard enough.  Let's work harder if we
                        # must evaluate.
                        operand.evaluation()
                return self.evaluation()
            raise EvaluationError(self)

        if self.exponent == one:
            return self.power_of_one_reduction()
        if (isinstance(self.exponent, Log)
            and self.base == self.exponent.base):
            # base_ns  = self.base.deduce_number_set()
            # antilog_ns = self.exponent.antilog.deduce_number_set()
            if (InSet(self.base, RealPos).proven()
                and InSet(self.exponent.antilog, RealPos).proven()
                and NotEquals(self.base, one).proven()):
                return self.power_of_log_reduction()
        if (isinstance(self.base, Exp) and
            isinstance(self.base.exponent, Div) and
            self.base.exponent.numerator == one and
                self.base.exponent.denominator == self.exponent):
            from . import nth_power_of_nth_root
            _n, _x = nth_power_of_nth_root.instance_params
            return nth_power_of_nth_root.instantiate(
                {_n: self.exponent, _x: self.base.base})
        elif (isinstance(self.base, Exp) and
            isinstance(self.exponent, Div) and
            self.exponent.numerator == one and
                self.exponent.denominator == self.base.exponent):
            from . import nth_root_of_nth_power, sqrt_of_square
            _n = self.base.exponent
            _x =  self.base.base
            if _n == two:
                return sqrt_of_square.instantiate({x: _x})
            return nth_root_of_nth_power.instantiate({n: _n, x: _x})
        expr = self
        # for convenience updating our equation:
        eq = TransRelUpdater(expr)
        if self.exponent == two and isinstance(self.base, Abs):
            from . import (square_abs_rational_simp,
                                     square_abs_real_simp)
            # |a|^2 = a if a is real
            try:
                deduce_number_set(self.base)
            except UnsatisfiedPrerequisites:
                pass
            rational_base = InSet(self.base, Rational).proven()
            real_base = InSet(self.base, Real).proven()
            thm = None
            if rational_base:
                thm = square_abs_rational_simp
            elif real_base:
                thm = square_abs_real_simp
            if thm is not None:
                simp = thm.instantiate({a: self.base.operand})
                expr = eq.update(simp)
                # A further simplification may be possible after
                # eliminating the absolute value.
                expr = eq.update(expr.simplification())

        return eq.relation

    @equality_prover('power_of_one_reduced', 'power_of_one_reduce')
    def power_of_one_reduction(self, **defaults_config):
        from . import complex_x_to_first_power_is_x
        if self.exponent != one:
            raise ValueError("'power_of_one_reduction' only applicable when "
                             "the exponent is 1, not %s"%self.exponent)
        return complex_x_to_first_power_is_x.instantiate({x: self.base})

    @equality_prover('power_of_log_reduced', 'power_of_log_reduce')
    def power_of_log_reduction(self, **defaults_config):
        from proveit.numbers import Log
        from . import exponent_log_with_same_base
        if (not isinstance(self.exponent, Log)
            or self.base != self.exponent.base):
            raise ValueError(
                    "Exp.power_of_log() method only applicable when "
                    "the exponent is a Log with base matching the Exp "
                    "base. Instead we have Exp base {0} and Exp "
                    "exponent {1}.".format(self.base, self.exponent))
        return exponent_log_with_same_base.instantiate(
                {a: self.base, x: self.exponent.antilog})

    @relation_prover
    def not_equal(self, other, **defaults_config):
        '''
        Attempt to prove that self is not equal to other.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers import zero
        if other == zero:
            return self.deduce_not_zero()
        # If it isn't a special case treated here, just use
        # conclude-as-folded.
        return NotEquals(self, other).conclude_as_folded()

    @relation_prover
    def deduce_not_zero(self, **defaults_config):
        '''
        Prove that this exponential is not zero given that
        the base is not zero.
        '''
        from proveit.logic import InSet
        from proveit.numbers import RationalPos
        from . import exp_rational_non_zero__not_zero, exp_not_eq_zero
        deduce_number_set(self.base)
        deduce_number_set(self.exponent)
        if (not exp_not_eq_zero.is_usable() or (
                InSet(self.base, RationalPos).proven() and
                InSet(self.exponent, RationalPos).proven())):
            # Special case where the base and exponent are RationalPos.
            return exp_rational_non_zero__not_zero.instantiate(
                {a: self.base, b: self.exponent})
        return exp_not_eq_zero.instantiate(
            {a: self.base, b: self.exponent})

    @equality_prover('expanded', 'expand')
    def expansion(self, **defaults_config):
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
            return square_expansion.instantiate({_x: self.base})

        if exponent == 3:
            from . import cube_expansion
            _x = cube_expansion.instance_param
            return cube_expansion.instantiate({_x: self.base})

        raise ValueError("Exp.expansion() implemented only for exponential "
                         "powers n=2 or n=3, but received an exponential "
                         "power of {0}.".format(exponent))

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factors, pull="left",
                      group_factors=True, group_remainder=False,
                      **defaults_config):
        '''
        Return the proven equality between the self Exp() and a
        factored form of self, pulling the factor(s) from the Exp to
        the "left" or "right". the_factors may be an iterable, a Mult, 
        or another Exp; in any case, the individual factors will be
        pulled together in the pull direction.
        Initially this factorization() method is quite simplistic,
        accepting as factors only factors expressed in terms of the
        original base used in the self Exp. For example, if
        self = 2^5, then only factors expressed as 2 or 2^r (with r
        a Real) are accepted as candidates, and except for the
        case where self=the_factors, the factorization is allowed
        to proceed literally --- for example, we can factor 2^8 out
        from 2^5 to obtain 2^5 = 2^8 2^{-3}. Because, why not?
        If group_factors is True, the factors are grouped together as
        a sub-product. If group_remainder is True and there are
        multiple remaining operands, then these remaining factors
        are grouped (actually right now there should always only be
        a single remaining factor, in the form a^b).
        '''
        from proveit import Expression, TransRelUpdater

        expr = self
        # A convenience for iteratively updating our equation,
        # beginning with self = self
        eq = TransRelUpdater(expr)

        # trivial or base case
        if the_factors == self:
            return eq.relation  # self = self

        from proveit.numbers.exponentiation import (
                exp_factored_int, exp_factored_real)

        if isinstance(the_factors, Expression): 
            # i.e. we have a single factor supplied rather than a
            # list of factors
            # Case (1) the_factors = self.base
            if (the_factors == self.base):
                # In both cases below, we turn off auto_simplify to
                # keep the Exp factors produce from being immediately
                # recombined on the rhs
                if InSet(self.base, RealPos).proven():
                    expr = eq.update(exp_factored_real.instantiate(
                            {a: self.base, b: self.exponent, c: one},
                            auto_simplify=False))
                elif (InSet(self.base, Real).proven()
                      and NotEquals(self.base, zero).proven()
                      and InSet(self.exponent, Integer).proven()):
                    expr = eq.update(exp_factored_int.instantiate(
                            {a: self.base, b: self.exponent, c: one},
                            auto_simplify=False))
                # then specifically simplify the a^1 to a
                expr = (eq.update(expr.inner_expr().operands[0].
                        simplification()))
                # then specifically simplify the a^{b-1} just in case
                # the (b-1) can be reduced
                expr = (eq.update(expr.inner_expr().operands[1].
                        simplification()))
                return eq.relation
            elif (isinstance(the_factors, Exp)
                  and (the_factors.base == self.base)):
                # we have a factor of a^c while self is a^b
                if InSet(self.base, RealPos).proven():
                    expr = eq.update(exp_factored_real.instantiate(
                            {a: self.base, b: self.exponent,
                             c: the_factors.exponent},
                            auto_simplify=False))
                elif (InSet(self.base, Real).proven()
                      and NotEquals(self.base, zero).proven()
                      and InSet(self.exponent, Integer).proven()
                      and InSet(the_factors.exponent, Integer).proven()):
                    expr = eq.update(exp_factored_int.instantiate(
                            {a: self.base, b: self.exponent,
                             c: the_factors.exponent},
                            auto_simplify=False))
                # then specifically simplify the a^{b-c} just in case
                # the (b-c) can be reduced
                expr = (eq.update(expr.inner_expr().operands[1].
                        simplification()))
                return eq.relation

            return eq.relation  # still self = self

        else:
            return eq.relation  # still self = self

    @equality_prover('distributed', 'distribute')
    def distribution(self, **defaults_config):
        '''
        Equate this exponential to a form in which the exponent
        is distributed over factors, or a power of a power reduces to
        a power of multiplied exponents.
        Examples:
            (a*b*c)^f = a^f * b^f * c^f
            (a/b)^f = (a^f / b^f)
            (a^b)^c = a^(b*c)
        '''
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
        deduce_number_set(exponent)
        if isinstance(base, Mult):
            if self.base.operands.is_double():
                _a, _b = self.base.operands
            else:
                _m = self.base.operands.num_elements()
                _a = self.base.operands
            if InSet(exponent, NaturalPos).proven():
                if self.base.operands.is_double():
                    return posnat_power_of_product.instantiate(
                        {a: _a, b: _b, n: exponent})
                else:
                    return posnat_power_of_products.instantiate(
                        {m: _m, a: _a, n: exponent})
            elif InSet(exponent, RealPos).proven():
                if self.base.operands.is_double():
                    return pos_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent})
                else:
                    return pos_power_of_products.instantiate(
                        {m: _m, a: _a, b: exponent})
            elif InSet(exponent, Real).proven():
                if self.base.operands.is_double():
                    return real_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent})
                else:
                    return real_power_of_products.instantiate(
                        {m: _m, a: _a, b: exponent})
            else:  # Complex is the default
                if self.base.operands.is_double():
                    return complex_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent})
                else:
                    return complex_power_of_products.instantiate(
                        {m: _m, a: _a, b: exponent})
        elif isinstance(base, Div):
            assert self.base.operands.is_double()
            _a, _b = self.base.operands
            if InSet(exponent, NaturalPos).proven():
                return posnat_power_of_quotient.instantiate(
                    {a: _a, b: _b, n: exponent})
            else:
                if InSet(exponent, RealPos).proven():
                    thm = pos_power_of_quotient
                elif InSet(exponent, Real).proven():
                    thm = real_power_of_quotient
                else:  # Complex is the default
                    thm = complex_power_of_quotient
                return thm.instantiate(
                    {a: _a, b: _b, c: exponent})
        elif isinstance(base, Exp):
            _a = base.base
            # if InSet(exponent, NaturalPos).proven():
            #     _m, _n = base.exponent, exponent
            #     return posnat_power_of_posnat_power.instantiate(
            #         {a: _a, m: _m, n: _n})
            # TRYING TO ANTICIPATE MORE POSSIBILITIES
            if InSet(exponent, NaturalPos).proven():
                if InSet(base.exponent, NaturalPos).proven():
                    _m, _n = base.exponent, exponent
                    return posnat_power_of_posnat_power.instantiate(
                        {a: _a, m: _m, n: _n})
                else:
                    _b, _c = base.exponent, exponent
                    if InSet(base.exponent, RealPos).proven():
                        thm = pos_power_of_pos_power
                    elif InSet(base.exponent, Real).proven():
                        thm = real_power_of_real_power
                    else:  # Complex is the default
                        thm = complex_power_of_complex_power
                    return thm.instantiate(
                        {a: _a, b: _b, c: _c})
            else:
                _b, _c = base.exponent, exponent
                if InSet(exponent, RealPos).proven():
                    thm = pos_power_of_pos_power
                elif InSet(exponent, Real).proven():
                    thm = real_power_of_real_power
                else:  # Complex is the default
                    thm = complex_power_of_complex_power
                return thm.instantiate(
                    {a: _a, b: _b, c: _c})
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

    @equality_prover('exp_factorized', 'exp_factor')
    def exp_factorization(self, exp_factor, **defaults_config):
        '''
        Pull out one of the exponent factors to an exponent at
        another level.  For example,
            a^{b*n} = (a^b)^n
            a^{-b*n} = (a^{-b})^n
        '''
        # Note: this is out-of-date.  Distribution handles this now,
        # except it doesn't deal with the negation part
        # (do we need it to?)
        from proveit.numbers import deduce_in_number_set, Neg
        # from .theorems import int_exp_of_exp, int_exp_of_neg_exp
        from . import int_exp_of_exp, int_exp_of_neg_exp
        if isinstance(self.exponent, Neg):
            b_times_c = self.exponent.operand
            thm = int_exp_of_neg_exp
        else:
            b_times_c = self.exponent
            thm = int_exp_of_exp
        # if not hasattr(b_times_c, 'factor'):
        #     raise ValueError('Exponent not factorable, may not raise the '
        #                      'exponent factor.')
        # factor_eq = b_times_c.factor(exp_factor, pull='right',
        #                              group_remainder=True,
        #                              assumptions=assumptions)
        if not hasattr(b_times_c, 'factorization'):
            raise ValueError('Exponent {0} not factorable (for example, it '
                             'does not appear to be in the Mult class); may '
                             'not raise the exponent factor.'.
                             format(b_times_c))
        factor_eq = b_times_c.factorization(exp_factor, pull='right',
                                     group_remainder=True)
        if factor_eq.lhs != factor_eq.rhs:
            # factor the exponent first, then raise this exponent factor
            factored_exp_eq = factor_eq.substitution(self)
            return factored_exp_eq.apply_transitivity(
                factored_exp_eq.rhs.exp_factorization(exp_factor))
        n_sub = b_times_c.operands[1]
        a_sub = self.base
        b_sub = b_times_c.operands[0]
        # deduce_not_zero(a_sub, assumptions)
        NotEquals(a_sub, zero).prove()
        # deduce_in_integer(n_sub, assumptions)
        deduce_in_number_set(n_sub, Integer)
        # deduce_in_complex([a_sub, b_sub], assumptions)
        deduce_in_number_set(a_sub, Complex)
        deduce_in_number_set(b_sub, Complex)
        return thm.instantiate({n: n_sub}).instantiate(
            {a: a_sub, b: b_sub}).derive_reversed()

    @equality_prover('exponent_separated', 'exponent_separate')
    def exponent_separation(self, **defaults_config):
        '''
        From self of the form x^{a+b} deduce and return the equality
        x^{a+b} = x^a x^b. For example,
            Exp(x, Add(two, c)).split_exponent_sum()
        (with the apprpriate assumptions) should return:
            |- (x^{2+c}) =  x^2 x^c.
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        # assumptions = defaults.checkedAssumptions(assumptions)

        from proveit.numbers import Add, Mult

        # implement only for the case in which exponent is an Add
        if not isinstance(self.exponent, Add):
            raise NotImplementedError(
            "'Exp.exponent_separation()' implemented only for cases in which "
            "the exponent appears as a sum (i.e. in the Add class). The "
            "exponent in this case is {0}.".format(self.exponent))

        # list the addends in the exponent, which become exponents
        the_exponents = self.exponent.operands

        # list the new exponential factors
        the_new_factors = [Exp(self.base, new_exp) if new_exp != one
                           else self.base for new_exp in the_exponents]

        # create the new equivalent product (Mult)
        mult_equiv = Mult(*the_new_factors)

        # use the Mult.exponent_combination() to deduce equality to self
        exp_separated = mult_equiv.exponent_combination()

        replacements = list(defaults.replacements)
        if defaults.auto_simplify:
            with Mult.temporary_simplification_directives() as tmp_directives:
                # Don't recombine the exponents after separating them.
                tmp_directives.combine_exponents = False
                replacements.append(mult_equiv.shallow_simplification())

        # reverse the equality relationship and return
        return exp_separated.derive_reversed(replacements=replacements,
                                             auto_simplify=False)


    """
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
    """

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Attempt to prove that this exponentiation expression is in the
        given number set.
        '''
        from proveit.logic import InSet, NotEquals
        from proveit.numbers.exponentiation import (
            exp_complex_closure, exp_natpos_closure, exp_int_closure,
            exp_rational_closure_nat_power, exp_rational_nonzero_closure,
            exp_rational_pos_closure, exp_real_closure_nat_power,
            exp_real_pos_closure, exp_real_non_neg_closure,
            exp_complex_closure, exp_complex_nonzero_closure,
            sqrt_complex_closure, sqrt_real_closure,
            sqrt_real_pos_closure, sqrt_real_non_neg_closure,
            sqrd_pos_closure, sqrd_non_neg_closure)

        from proveit.numbers import zero

        deduce_number_set(self.exponent)
        if number_set == NaturalPos:
            return exp_natpos_closure.instantiate(
                {a: self.base, b: self.exponent})
        elif number_set == Natural:
            # Use the NaturalPos closure which applies for
            # any Natural base and exponent.
            self.deduce_in_number_set(NaturalPos)
            return InSet(self, Natural).prove()
        elif number_set == Integer:
            return exp_int_closure.instantiate(
                {a: self.base, b: self.exponent})
        elif number_set == Rational:
            power_is_nat = InSet(self.exponent, Natural)
            if not power_is_nat.proven():
                # Use the RationalNonZero closure which works
                # for negative exponents as well.
                self.deduce_in_number_set(RationalNonZero)
                return InSet(self, Rational).prove()
            return exp_rational_closure_nat_power.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == RationalNonZero:
            return exp_rational_nonzero_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == RationalPos:
            return exp_rational_pos_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == Real:
            if self.exponent == frac(one, two):
                return sqrt_real_closure.instantiate(
                    {a: self.base, b: self.exponent})
            else:
                power_is_nat = InSet(self.exponent, Natural)
                if not power_is_nat.proven():
                    # Use the RealPos closure which allows
                    # any real exponent but requires a
                    # non-negative base.
                    self.deduce_in_number_set(RealPos)
                    return InSet(self, Real).prove()
                return exp_real_closure_nat_power.instantiate(
                        {a: self.base, b: self.exponent})
        elif number_set == RealPos:
            if self.exponent == frac(one, two):
                return sqrt_real_pos_closure.instantiate({a: self.base})
            elif self.exponent == two:
                return sqrd_pos_closure.instantiate({a: self.base})
            else:
                return exp_real_pos_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == RealNonNeg:
            if self.exponent == frac(one, two):
                return sqrt_real_non_neg_closure.instantiate({a: self.base})
            elif self.exponent == two:
                return sqrd_non_neg_closure.instantiate({a: self.base})
            else:
                return exp_real_non_neg_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == Complex:
            if self.exponent == frac(one, two):
                return sqrt_complex_closure.instantiate(
                    {a: self.base})
            else:
                return exp_complex_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == ComplexNonZero:
            return exp_complex_nonzero_closure.instantiate(
                    {a: self.base, b: self.exponent})

        raise NotImplementedError(
            "'Exp.deduce_in_number_set' not implemented for the %s set"
            % str(number_set))

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        For simple cases, deduce a bound on this Exp object given a
        bound on its operand. For example, suppose x = Exp(y, 2) and
        we know that y >= 2. Then x.bound_via_operand_bound(y >= 2)
        returns x >= 2^2 = 4.
        This method currently works MAINLY for expressions
        of the form Exp(x, a) for non-negative real x and real exponent
        'a', where we know something of the form x < y (or x ≤ y, x > y,
        x ≥ y) involving the base of the exponential expression.
        The result also depends on knowing the relationship between the
        exponent 'a' and zero, which might need to be pre-proven or
        provided as an assumption (e.g. in the form 'a > 0' or
        InSet(a, RealNeg), etc).
        A special case also deals with a negative base raised to the
        power of 2.
        This method also works for special cases of the form Exp(a, x),
        where a > 1 and the operand_relation involve the exponent x.

        Future development will address operand_relations
        involving the exponent x in expressions of the form a^x when
        the base 0 < a < 1, and expand the special negative
        base case to include all even and odd exponent cases.
        Also see NumberOperation.deduce_bound and compare to the
        bound_via_operand_bound() method found in the Div and Neg
        classes.
        '''
        from proveit import Judgment
        from proveit.numbers import (
                two, greater, greater_eq, Less, LessEq,
                NumberOrderingRelation, RealNonNeg)
        if isinstance(operand_relation, Judgment):
            operand_relation = operand_relation.expr
        if not isinstance(operand_relation, NumberOrderingRelation):
            raise TypeError(
                    "In Exp.bound_via_operand_bound(), the "
                    "'operand_relation' argument is expected to be a number "
                    "relation (<, >, ≤, or ≥), but instead was {}.".
                    format(operand_relation))

        lhs = operand_relation.lhs
        # should be able to generalize this later
        # no need to limit to just lhs, right?
        if lhs != self.base and lhs != self.exponent:
            raise ValueError(
                    "In Exp.bound_via_operand_bound(), the left side of "
                    "the 'operand_relation' argument {0} is expected to "
                    "match either the Exp base operand {1} or the "
                    "Exp exponent operand {2}.".
                    format(operand_relation, self.base, self.exponent))

        # assign x and y subs according to std Less or LessEq relations
        _x_sub = operand_relation.normal_lhs
        _y_sub = operand_relation.normal_rhs
        if lhs == self.base:
            _a_sub = self.exponent
        else:
            _a_sub = self.base

        # I. Default case: the user-supplied operand relation involves
        #    the BASE of the Exp expression x^a
        if lhs == self.base:

            # Several cases to consider:
            #  (1) a > 0, 0 ≤ x < y
            #  (2) a > 0, 0 ≤ x ≤ y
            #  (3) a ≥ 0, 0 < x < y
            #  (4) a ≥ 0, 0 < x ≤ y
            #  (5) a < 0, 0 < x < y
            #  (6) a < 0, 0 < x ≤ y
            #  (7) a ≤ 0, 0 < x < y
            #  (8) a ≤ 0, 0 < x ≤ y
            # =====================
            #  (9) a = 2, y < x < 0
            # (10) a = 2, y ≤ x < 0

            # Cases (1) and (2): exponent a > 0
            if (greater(_a_sub, zero).proven() and
                greater_eq(_x_sub, zero).proven()):
                if isinstance(operand_relation, Less):
                    from proveit.numbers.exponentiation import exp_pos_less
                    bound = exp_pos_less.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                elif isinstance(operand_relation, LessEq):
                    from proveit.numbers.exponentiation import exp_pos_lesseq
                    bound = exp_pos_lesseq.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                else:
                    raise TypeError(
                        "In Exp.bound_via_operand_bound(), the 'operand_relation' "
                        "argument is expected to be a 'Less', 'LessEq', 'greater', "
                        "or 'greater_eq' relation. Instead we have {}.".
                        format(operand_relation))

            # Cases (3) and (4): exponent a ≥ 0
            elif (greater_eq(_a_sub, zero).proven() and
                greater(_x_sub, zero).proven()):
                if isinstance(operand_relation, Less):
                    from proveit.numbers.exponentiation import exp_nonneg_less
                    bound = exp_nonneg_less.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                elif isinstance(operand_relation, LessEq):
                    from proveit.numbers.exponentiation import exp_nonneg_lesseq
                    bound = exp_nonneg_lesseq.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                else:
                    raise TypeError(
                        "In Exp.bound_via_operand_bound(), the 'operand_relation' "
                        "argument is expected to be a 'Less', 'LessEq', 'greater', "
                        "or 'greater_eq' relation. Instead we have {}.".
                        format(operand_relation))

            # Cases (5) and (6): exponent a < 0
            elif (Less(_a_sub, zero).proven() and
                greater(_x_sub, zero).proven()):
                if isinstance(operand_relation, Less):
                    from proveit.numbers.exponentiation import exp_neg_less
                    bound = exp_neg_less.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                elif isinstance(operand_relation, LessEq):
                    from proveit.numbers.exponentiation import exp_neg_lesseq
                    bound = exp_neg_lesseq.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                else:
                    raise TypeError(
                        "In Exp.bound_via_operand_bound(), the 'operand_relation' "
                        "argument is expected to be a 'Less', 'LessEq', 'greater', "
                        "or 'greater_eq' relation. Instead we have {}.".
                        format(operand_relation))

            # Cases (7) and (8): exponent a ≤ 0
            elif (LessEq(_a_sub, zero).proven() and
                greater(_x_sub, zero).proven()):
                if isinstance(operand_relation, Less):
                    from proveit.numbers.exponentiation import exp_nonpos_less
                    bound = exp_nonpos_less.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                elif isinstance(operand_relation, LessEq):
                    from proveit.numbers.exponentiation import exp_nonpos_lesseq
                    bound = exp_nonpos_lesseq.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                else:
                    raise TypeError(
                        "In Exp.bound_via_operand_bound(), the 'operand_relation' "
                        "argument is expected to be a 'Less', 'LessEq', 'greater', "
                        "or 'greater_eq' relation. Instead we have {}.".
                        format(operand_relation))

            # Cases (9) and (10): exponent a = 2
            # with x < y < 0 or x ≤ y < 0

            elif (_a_sub == two and
                Less(_y_sub, zero).proven()):
                if isinstance(operand_relation, Less):
                    from proveit.numbers.exponentiation import (
                            exp_even_neg_base_less)
                    bound = exp_even_neg_base_less.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                elif isinstance(operand_relation, LessEq):
                    from proveit.numbers.exponentiation import (
                            exp_even_neg_base_lesseq)
                    bound = exp_even_neg_base_lesseq.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                else:
                    raise TypeError(
                        "In Exp.bound_via_operand_bound(), the 'operand_relation' "
                        "argument is expected to be a 'Less', 'LessEq', 'greater', "
                        "or 'greater_eq' relation. Instead we have {}.".
                        format(operand_relation))

            else:
                raise ValueError(
                        "In calling Exp.bound_via_operand_bound(), a "
                        "specific matching case was not found for {}.".
                        format(self))

        # II. 2nd main case: the user-supplied operand relation involves
        #    the EXPONENT of the Exp expression a^x
        elif lhs == self.exponent:

            # Several cases to consider (others to be developed)
            # considering the Exp expression a^x with a, x in Real:
            #  (1) a > 1, x < y
            #  (2) a > 1, x ≤ y
            #  (3) a > 1, y < x
            #  (4) a > 1, y ≤ x
            # Other cases to be developed involving base a < 1,
            # which produces a monotonically-decreasing function.

            # Cases (1)-(4): base a > 1, a^x monotonically increasing
            if (greater(_a_sub, one).proven() and
                InSet(_x_sub, Real).proven()):
                if isinstance(operand_relation, Less):
                    from proveit.numbers.exponentiation import (
                            exp_monotonicity_large_base_less)
                    bound = exp_monotonicity_large_base_less.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                elif isinstance(operand_relation, LessEq):
                    from proveit.numbers.exponentiation import (
                        exp_monotonicity_large_base_less_eq)
                    bound = exp_monotonicity_large_base_less_eq.instantiate(
                            {x: _x_sub, y: _y_sub, a: _a_sub})
                else:
                    raise TypeError(
                        "In Exp.bound_via_operand_bound(), the 'operand_relation' "
                        "argument is expected to be a 'Less', 'LessEq', 'greater', "
                        "or 'greater_eq' relation. Instead we have {}.".
                        format(operand_relation))
            else:
                raise ValueError(
                        "In Exp.bound_via_operand_bound(), either the "
                        "base {0} is not known to be greater than 1 and/or "
                        "the operand {1} is not known to be Real.".
                        format(_a_sub, _x_sub))

        else:
            raise ValueError("OOOPS!")

        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most
        restrictive standard number set we can readily know.
        '''
        base_ns = deduce_number_set(self.base).domain
        exp_ns = deduce_number_set(self.exponent).domain
        if Natural.includes(base_ns) and Natural.includes(exp_ns):
            return self.deduce_in_number_set(NaturalPos)
        if Integer.includes(base_ns) and Natural.includes(exp_ns):
            return self.deduce_in_number_set(Integer)
        if RationalPos.includes(base_ns) and Integer.includes(exp_ns):
            return self.deduce_in_number_set(RationalPos)
        if (RationalNonZero.includes(base_ns)
                and Integer.includes(exp_ns)):
            return self.deduce_in_number_set(RationalNonZero)
        if Rational.includes(base_ns) and Natural.includes(exp_ns):
            return self.deduce_in_number_set(Rational)
        if RealPos.includes(base_ns) and Real.includes(exp_ns):
            return self.deduce_in_number_set(RealPos)
        if RealNonNeg.includes(base_ns) and Real.includes(exp_ns):
            return self.deduce_in_number_set(RealNonNeg)
        if Real.includes(base_ns) and Natural.includes(exp_ns):
            return self.deduce_in_number_set(Real)
        if ComplexNonZero.includes(base_ns):
            return self.deduce_in_number_set(ComplexNonZero)
        return self.deduce_in_number_set(Complex)


class ExpSetMembership(SetMembership):
    '''
    Defines methods that apply to membership in an exponentiated set.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)
        self.domain = domain

    @prover
    def conclude(self, **defaults_config):
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
                elem_in_set, defaults.assumptions,
                "Can only automatically deduce membership in exponentiated "
                "sets for an element that is a list")
        exponent_eval = domain.exponent.evaluation()
        exponent = exponent_eval.rhs
        base = domain.base
        if is_literal_int(exponent):
            if exponent == zero:
                return exp_set_0.instantiate({S: base})
            if element.num_entries() != exponent.as_int():
                raise ProofFailure(
                    elem_in_set, defaults.assumptions,
                    "Element not a member of the exponentiated set; "
                    "incorrect list length")
            elif exponent in DIGITS:
                # thm = forall_S forall_{a, b... in S} (a, b, ...) in S^n
                thm = locals()['exp_set_%d' % exponent.as_int()]
                expr_map = {S: base}  # S is the base
                # map a, b, ... to the elements of element.
                expr_map.update({proveit.__getattr__(
                    chr(ord('a') + _k)): elem_k for _k, elem_k
                    in enumerate(element)})
                elem_in_set = thm.instantiate(expr_map)
            else:
                raise ProofFailure(
                    elem_in_set, defaults.assumptions,
                    "Automatic deduction of membership in exponentiated sets "
                    "is not supported beyond an exponent of 9")
        else:
            raise ProofFailure(
                elem_in_set, defaults.assumptions,
                "Automatic deduction of membership in exponentiated sets is "
                "only supported for an exponent that is a literal integer")
        if exponent_eval.lhs != exponent_eval.rhs:
            # after proving that the element is in the set taken to
            # the evaluation of the exponent, substitute back in the
            # original exponent.
            return exponent_eval.sub_left_side_into(elem_in_set)
        return elem_in_set

    def side_effects(self, judgment):
        return
        yield

# outside any specific class:
# special Exp case of square root

def exp(exponent, *, styles=None):
    from proveit.numbers import e # Euler's number
    return Exp(e, exponent, styles=styles)

def exp2pi_i(*exp_factors):
    from proveit.numbers import Mult, pi, i
    return exp(Mult(*((two, pi, i) + exp_factors)))

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
