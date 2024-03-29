from proveit import (defaults, equality_prover, ExprRange, ExprTuple,
                     Function,
                     InnerExpr, Literal, maybe_fenced_string,
                     SimplificationDirectives,
                     ProofFailure, prover, relation_prover, StyleOptions,
                     UnsatisfiedPrerequisites, USE_DEFAULTS)
import proveit
from proveit import a, b, c, d, k, m, n, r, x, y, S, theta
from proveit.logic import Equals, InSet, SetMembership, NotEquals
from proveit.numbers import zero, one, two, Div, frac, num, greater_eq
from proveit.numbers import (NumberOperation, deduce_number_set,
                             readily_provable_number_set)
from proveit.numbers.number_sets import (
    ZeroSet, Natural, NaturalPos,
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

    _simplification_directives_ = SimplificationDirectives(
            reduce_double_exponent = True,
            distribute_exponent = False,
            factor_numeric_rational = False)

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

    def _build_canonical_form(self):
        '''
        The canonical form of an Exp will address:
            x^0 = 1
            x^1 = x
            (x*y*z)^a = x^a * y^a * z^a
            (x^a)^b = x^(a*b) if a and b are numeric rationals.
            x^{2n} = (-x)^{2n} if 2n is a numeric even number (2, 4, ..)
        Also, raising a literal rational to an integer power equates
        to a irreducible rational.
        Some of these equalities require the base of the exponent
        to be nonzero, but these should work as long as the expression
        is not a garbage expression.
        '''
        from proveit.numbers import (one, zero, Add, Neg, Mult, 
                                     is_numeric_rational, is_numeric_int,
                                     numeric_rational_ints,
                                     simplified_numeric_rational)
        base = self.base.canonical_form()
        exponent = self.exponent.canonical_form()
        if exponent == zero:
            return one # x^0 = 1
        elif exponent == one:
            return base # x^1 = x
        elif isinstance(base, Mult):
            # (x*y*z)^a = x^a * y^a * z^a
            factors = []
            for factor in base.factors:
                if isinstance(factor, ExprRange):
                    factor = ExprRange(factor.parameter,
                                       Exp(factor.body, exponent),
                                       factor.true_start_index,
                                       factor.true_end_index)
                else:
                    factor = Exp(factor, exponent)
                factors.append(factor)
            return Mult(*factors).canonical_form()
            # return Mult(*[Exp(factor, exponent) for factor 
            #               in base.factors])
        elif isinstance(base, Exp):
            # (x^a)^b = x^(a*b)
            exponent = Mult(base.exponent, exponent).canonical_form()
            if exponent == one:
                return base.base
            return Exp(base.base, exponent).canonical_form()
        elif is_numeric_rational(base) and is_numeric_int(exponent):
            # Raising a numeric rational to an integer power.
            numer, denom = numeric_rational_ints(base)
            if isinstance(exponent, Neg):
                # A negative power will flip the numerator
                # and denominator.
                numer, denom = denom, numer
                exponent = exponent.operand
            numer = numer**(exponent.as_int())
            denom = denom**(exponent.as_int())
            return simplified_numeric_rational(numer, denom)
        elif is_numeric_rational(base) and (
                isinstance(exponent, Add) and 
                any(is_numeric_rational(_term) for _term 
                    in exponent.operands.entries)):
            # Raising a numeric rational to a power with a numeric
            # rational term; factor out the numeric rational via
            # a^{x + b} = a^b * a^x
            numeric_exp_terms = [_term for _term in exponent.terms.entries
                                 if is_numeric_rational(_term)]
            nonnumeric_exp_terms = [_term for _term in exponent.terms.entries
                                    if not is_numeric_rational(_term)]
            assert len(numeric_exp_terms)==1
            return Mult(Exp(base, numeric_exp_terms[0]).canonical_form(),
                        Exp(base, Add(*nonnumeric_exp_terms)).canonical_form())
        elif is_numeric_int(exponent) and (exponent.as_int() % 2 == 0):
            # x^{2n} = (-x)^{2n}, so choose one of these forms 
            # deterministically.
            from proveit.numbers import Abs
            # reuse code dealing with |x| = |-x|:
            base = Abs(base).canonical_form().operand
        if base != self.base or exponent != self.exponent:
            # Use the canonical forms of the base and exponent.
            return Exp(base, exponent)
        return self

    def _deduce_canonically_equal(self, rhs):
        '''
        Prove equality of Exp asssuming they have the same canonical
        form.
        '''
        from proveit.numbers import Neg, Mult, num, is_numeric_int
        base = self.base
        exponent = self.exponent
        if isinstance(rhs, Exp) and (
                exponent == rhs.exponent and 
                is_numeric_int(self.exponent) and
                exponent.as_int() % 2 == 0 and (
                        Neg(base).canonical_form() ==
                        rhs.base.canonical_form())):
            # This is a x^{2n} = (-x)^{2n} case.
            from . import even_pow_is_even_fn_rev
            _x = base
            _n = num(exponent.as_int()//2)
            replacements = []
            replacements.append(Equals(Mult(two, _n), exponent).prove())
            replacements.append(Equals(Neg(_x), rhs.base).prove())
            return even_pow_is_even_fn_rev.instantiate(
                    {x:_x, n:_n}, replacements=replacements,
                    auto_simplify=False)
        
        # Prove equality using standard techniques.
        return NumberOperation._deduce_canonically_equal(self, rhs)        
        
    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Exp
        expression assuming the operands have been simplified.

        Handles the following simplifications:
            a^0 = 1 for any complex a
            0^x = 0 for any positive x
            1^x = 1 for any complex x
            a^(Log(a, x)) = x for RealPos a and x, a != 1.
            x^n = x*x*...*x = ? for a natural n and irreducible x.
            (-x)^2 = x^2 or any even, numeric power
        
        Additionally may do the following depending upon simplification
        directives:
            * If reduce_double_exponent is True:
                (x^y)^z = x^{y*z}
            * If distribute_exponent is True:
                (a*b*c)^f = a^f * b^f * c^f
                (a/b)^f = (a^f / b^f)
            * If factor_numeric_rational is True:
                a^{x+b} = a^b a^x if a and b are numeric rationals.
        '''
        from proveit.relation import TransRelUpdater
        from proveit.logic import is_irreducible_value
        from proveit.logic import InSet
        from proveit.numbers import (zero, one, two, Add, Neg, Mult, Div,
                                     is_numeric_int, is_numeric_rational,
                                     numeric_rational_ints,
                                     Log, Rational, Abs)
        from . import (exp_zero_eq_one, exponentiated_zero,
                       exponentiated_one, exp_nat_pos_expansion)

        if self.is_irreducible_value():
            # already irreducible
            return Equals(self, self).conclude_via_reflexivity()

        if must_evaluate:
            if not all(is_irreducible_value(operand) for
                       operand in self.operands):
                for operand in self.operands:
                    if not is_irreducible_value(operand):
                        # The simplification of the operands may not have
                        # worked hard enough.  Let's work harder if we
                        # must evaluate.
                        operand.evaluation()
                return self.evaluation()
        
        base, exponent = self.base, self.exponent
        if is_numeric_rational(base):
            _a, _b = numeric_rational_ints(base)

        if exponent == zero:
            return exp_zero_eq_one.instantiate({a: base})  # =1
        elif base == zero:
            # Will fail if the exponent is not positive, but this
            # is the only sensible thing to try.
            return exponentiated_zero.instantiate({x: exponent})  # =0
        elif exponent == one:
            return self.power_of_one_reduction()
        elif base == one:
            return exponentiated_one.instantiate({x: exponent})  # =1
        elif (isinstance(base, Exp) and (
                isinstance(base.exponent, Div) and
                base.exponent.numerator == one and
                base.exponent.denominator == exponent and
                greater_eq(base.base, zero).readily_provable() and
                InSet(exponent, NaturalPos).readily_provable())):
            from . import nth_power_of_nth_root
            return nth_power_of_nth_root.instantiate(
                {n: exponent, x: base.base})
        elif (isinstance(base, Exp) and (
                isinstance(exponent, Div) and
                exponent.numerator == one and
                exponent.denominator == base.exponent and
                (base.exponent == two or
                 (greater_eq(base.base, zero).readily_provable()) and
                 InSet(base.exponent, NaturalPos).readily_provable()))):
            from . import nth_root_of_nth_power, sqrt_of_square
            _n = base.exponent
            _x =  base.base
            if _n == two:
                return sqrt_of_square.instantiate({x: _x})
            return nth_root_of_nth_power.instantiate({n: _n, x: _x})
        elif (is_numeric_rational(base) and
                  is_numeric_int(exponent) and
                  exponent.as_int() > 1):
            # exponentiate a rational to a positive integer
            expr = self
            eq = TransRelUpdater(expr)
            expr = eq.update(exp_nat_pos_expansion.instantiate(
                    {x:base, n:exponent}, preserve_all=True))
            # We should come up with a better way of reducing
            # ExprRanges representing repetitions:
            _n = self.exponent.as_int()
            if _n <= 0 or _n > 9:
                raise NotImplementedError("Currently only implemented for 1-9")
            repetition_thm = proveit.numbers.numerals.decimals \
                .__getattr__('reduce_%s_repeats' % _n)
            rep_reduction = repetition_thm.instantiate({x: base})
            expr = eq.update(expr.inner_expr().operands.substitution(
                    rep_reduction.rhs, preserve_all=True))
            expr = eq.update(expr.evaluation())
            return eq.relation
        elif (is_numeric_rational(base) and _b != 0 and
                  is_numeric_int(exponent) and
                  exponent.as_int() < 0):
            # exponentiate a rational to a negative integer
            # _a and _b are the numerator and denominator as ints.
            from proveit.numbers.exponentiation import (
                    neg_power_as_div, neg_power_of_quotient)
            _n = num(-exponent.as_int())
            if _b == 1:
                return neg_power_as_div.instantiate({a:num(_a), n:_n})
            else:
                return neg_power_of_quotient.instantiate(
                        {a:num(_a), b:num(_b), n:_n})
        elif (isinstance(exponent, Log)
            and base == exponent.base):
            # base_ns  = base.deduce_number_set()
            # antilog_ns = exponent.antilog.deduce_number_set()
            if InSet(base, RealPos).readily_provable() and (
                    InSet(exponent.antilog, RealPos).readily_provable()
                    and NotEquals(base, one).readily_provable()):
                return self.power_of_log_reduction()
        elif exponent == two and isinstance(base, Abs) and (
                InSet(base.operand, Real).readily_provable()):
            from . import (square_abs_rational_simp,
                                     square_abs_real_simp)
            # |a|^2 = a if a is real
            expr = self
            # for convenience updating our equation:
            eq = TransRelUpdater(expr)
            base_ns = readily_provable_number_set(base, 
                                                  default=Complex)
            rational_base = Rational.readily_includes(base_ns)
            real_base = Real.readily_includes(base_ns)
            thm = None
            if rational_base:
                thm = square_abs_rational_simp
            elif real_base:
                thm = square_abs_real_simp
            if thm is not None:
                simp = thm.instantiate({a: base.operand})
                expr = eq.update(simp)
                # A further simplification may be possible after
                # eliminating the absolute value.
                expr = eq.update(expr.simplification())
            return eq.relation
        elif isinstance(base, Neg) and is_numeric_int(exponent) and (exponent.as_int() % 2 == 0):
            # (-x)^2 = x^2, (-x)^4 = x^4, etc.
            from . import even_pow_is_even_fn
            _n = num(exponent.as_int()//2)
            replacements = []
            replacements.append(Equals(Mult(two, _n), exponent).prove())
            return even_pow_is_even_fn.instantiate(
                    {x:base.operand, n:_n}, replacements=replacements)        
        elif isinstance(base, Exp) and (
                Exp._simplification_directives_.reduce_double_exponent):
            if ((InSet(exponent, Real).readily_provable() and 
                 InSet(base.exponent, Real).readily_provable() and
                 NotEquals(base.base, zero).readily_provable()) or (
                         InSet(base.base, RealPos).readily_provable())):
                # (a^b)^c = a^{b*c}
                return self.double_exponent_reduction()
        if Exp._simplification_directives_.distribute_exponent and (
                isinstance(base, Mult) or isinstance(base, Div)):
            # Distribute the exponent as directed.
            return self.distribution(auto_simplify=True)
        elif Exp._simplification_directives_.factor_numeric_rational:
            # a^{x+b} = a^b a^x if a and b are numeric rationals
            if is_numeric_rational(base) and (
                    isinstance(exponent, Add) and 
                    any(is_numeric_rational(_term) for _term 
                        in exponent.operands.entries)):
                # The base and one of the exponent terms is a numeric
                # rational.
                expr = self
                eq = TransRelUpdater(expr)
                # Pull numeric rationals to the front of the exponent
                # terms.
                with Add.temporary_simplification_directives() as _tmp_drvs:
                    _tmp_drvs.ungroup = False
                    _tmp_drvs.combine_like_terms = False
                    _tmp_drvs.order_key_fn = lambda term : (
                            0 if is_numeric_rational(term) else 1)
                    expr = eq.update(
                            expr.inner_expr()
                            .exponent.shallow_simplification())
                # Associate into two terms: numeric rationals and
                # everything else.
                for _k, _term in enumerate(expr.exponent.terms.entries):
                    if not is_numeric_rational(_term):
                        break
                _terms = expr.exponent.terms
                _num_terms = _terms.num_entries()
                if _k < _num_terms:
                    if _k+1 < expr.exponent.terms.num_entries():
                        expr = eq.update(
                                expr.inner_expr().exponent.association(
                                        _k, _num_terms-_k, preserve_all=True))
                    if _k > 1:
                        expr = eq.update(
                                expr.inner_expr().exponent.association(
                                        0, _k, auto_simplify=False))
                expr = eq.update(expr.exponent_separation(preserve_all=True))
                eq.update(expr.inner_expr().factors[0].simplification())
                return eq.relation
                    
        return Equals(self, self).conclude_via_reflexivity()
    
    def is_irreducible_value(self):
        '''
        This needs work, but we know that sqrt(2) is irreducible as
        a special case.
        '''
        if isinstance(self.exponent, Div):
            if self.exponent == frac(one, two):
                if self.base == two:
                    return True
        return False # TODO: handle more cases.

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
    def deduce_equal(self, other, **defaults_config):
        '''
        Attempt to prove that self is equal to other.
        Handles r exp(i theta) = r. 
        '''
        from proveit.numbers import complex_polar_coordinates
        reductions = set()
        try:
            _r, _theta = complex_polar_coordinates(
                    self, reductions=reductions)
        except ValueError:
            _r = _theta = None
        if _theta is not None:
            if _r == other:
                # r exp(i theta) = r if theta/(2 pi) is an integer
                if _r == one:
                    from . import unit_complex_polar_num_eq_one
                    return unit_complex_polar_num_eq_one.instantiate(
                            {theta: _theta}, replacements=reductions)
                else:
                    from . import complex_polar_num_eq_one
                    return complex_polar_num_eq_one.instantiate(
                            {r: _r, theta: _theta}, replacements=reductions)
        raise NotImplementedError(
                "deduce_equal case not handled: %s ≠ %s"%
                (self, other))

    def readily_not_equal(self, other):
        '''
        Return True if we can readily prove 'self' is not 'other'.
        Handles a^b ≠ 0 and exp(i theta) ≠ 1. 
        '''
        from proveit.numbers import Mult, Neg, e, i
        if other == zero:
            # a^b ≠ 0 or a ≠ 0 
            return NotEquals(self.base, zero).readily_provable()
        if other == one and self.base == e:
            exponent = self.exponent
            if isinstance(exponent, Neg):
                # exp(i theta) ≠ 1 if and only if exp(-i theta) ≠ 1,
                # so the sign doesn't matter.
                exponent = exponent.operand
            if self.exponent == i:
                return True # exp(i) ≠ 1
            if isinstance(exponent, Mult):
                exponent_factors = exponent.operands.entries
                if i not in exponent_factors:
                    return False
                i_idx = exponent_factors.index(i)
                theta_factors = [f for _idx, f in enumerate(exponent_factors)
                                 if _idx != i_idx]
                if InSet(Mult(*theta_factors), Real).readily_provable():
                    return True                
        return False            

    @relation_prover
    def deduce_not_equal(self, other, **defaults_config):
        '''
        Attempt to prove that self is not equal to other.
        Handles a^b ≠ 0 and exp(i theta) ≠ 1. 
        '''
        from proveit.numbers import zero, complex_polar_coordinates
        #from . import 
        if other == zero:
            return self.deduce_not_zero()
        reductions = set()
        try:
            _r, _theta = complex_polar_coordinates(
                    self, reductions=reductions)
        except ValueError:
            _r = _theta = None
        if _theta is not None:
            if _r == other:
                # r exp(i theta) ≠ r if theta/(2 pi) is not an integer
                if _r == one:
                    from . import unit_complex_polar_num_neq_one
                    return unit_complex_polar_num_neq_one.instantiate(
                            {theta: _theta}, replacements=reductions)
                else:
                    from . import complex_polar_num_neq_one
                    return complex_polar_num_neq_one.instantiate(
                            {r: _r, theta: _theta}, replacements=reductions)
        raise NotImplementedError(
                "deduce_not_equal case not handled: %s ≠ %s"%
                (self, other))

    @relation_prover
    def deduce_not_zero(self, **defaults_config):
        '''
        Prove that this exponential is not zero given that
        the base is not zero.
        '''
        from proveit.numbers import readily_provable_number_set, RationalPos
        from . import exp_rational_non_zero__not_zero, exp_not_eq_zero
        base_ns = readily_provable_number_set(self.base, default=Complex)
        exp_ns = readily_provable_number_set(self.exponent, default=Complex)
        if (not exp_not_eq_zero.is_usable() or (
                RationalPos.readily_includes(base_ns) and
                RationalPos.readily_includes(exp_ns))):
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

    def readily_factorable(self, factor):
        '''
        Return True iff 'factor' is factorable from 'self' in an
        obvious manner.  For this Exp, a^b is readily factorable
        from c^d if a is factorable from c and either
        d >= b >= 0 or d <= b <= 0 is readily provable.
        '''
        from proveit.numbers import (zero, one, LessEq, Mult, Neg,
                                     readily_factorable)
        if self == factor:
            return True
        if isinstance(factor, Div):
            # Convert a/b to a*b^{-1}
            if factor.numerator==one:
                factor = Exp(factor.denominator, Neg(one))
            else:
                factor = Mult(factor.numerator, 
                              Exp(factor.denominator, Neg(one)))
        if isinstance(factor, Exp):
            factor_base = factor.base
            if readily_factorable(self.base, factor_base):
                for ineq_type in (greater_eq, LessEq):
                    if ineq_type(self.exponent, 
                                 factor.exponent).readily_provable() and (
                            ineq_type(factor.exponent, 
                                      zero).readily_provable()):
                        # a^b factorable from c^d because a is factorable
                        # from c and d >= b.
                        return True
        if readily_factorable(self.base, factor):
            if greater_eq(self.exponent, one).readily_provable():
                # a factorable from c^d because a is factorable
                # from c and d >= 1.
                return True
        return False

    @equality_prover('factorized', 'factor')
    def factorization(self, factor, pull="left",
                      group_factors=True, group_remainder=False,
                      **defaults_config):
        '''
        Return the proven factorization (equality with the factored
        form) from pulling the factor(s) from this exponentiation to 
        the "left" or "right".  Examples:
            (a*b)^c = (a^c)*(b^c), pulling a^c to the left or
                                   pulling b^c to the right
            (a*b)^c = (a^d)*(a^{d-c})(b^c) pulling a^d to the left
            (a*b)^c = a*((a^{c-1})*(b^c)) pulling a to the left with
                                          group_remainder=True.
        '''
        from proveit import Expression, TransRelUpdater
        from proveit.numbers import Mult, subtract, readily_factorable
        from proveit.numbers.exponentiation import (
                exp_factored_int, exp_factored_real)

        expr = self
        # A convenience for iteratively updating our equation,
        # beginning with self = self
        eq = TransRelUpdater(expr)

        # trivial or base case
        if factor == self:
            return eq.relation  # self = self
        
        if isinstance(factor, Div):
            reduction = factor.reduction_to_mult()
            factor = reduction.rhs
            replacements = [reduction.derive_reversed()]
            return self.factorization(
                    factor, pull=pull, group_factors=group_factors,
                    group_remainder=group_remainder,
                    replacements=replacements)

        base_ns = readily_provable_number_set(self.base, default=Complex)
        exp_ns = readily_provable_number_set(self.exponent, default=Complex)
        if not isinstance(factor, Expression): 
            raise TypeError("Expecting 'factor' to be an Expression")            
        
        
        with Mult.temporary_simplification_directives() as tmp_directives:
            # Prevent exponents from re-combining as we factor them out.
            tmp_directives.combine_numeric_rational_exponents=False
            tmp_directives.combine_all_exponents=False
            
            replacements = None
            if (factor == self.base):
                if self.exponent == one:
                    # Special case factoring a out of a^1 as a^1 = 1.
                    return self.power_of_one_reduction()
                factor_base = factor
                _b, _c, _d = self.exponent, one, subtract(self.exponent, one)
                replacements = [Exp(factor, one).power_of_one_reduction()]
            elif isinstance(factor, Exp) and factor.base == self.base:
                factor_base = factor.base
                _b, _c, _d = self.exponent, factor.exponent, (
                        subtract(self.exponent, factor.exponent))
                replacements = []
            if replacements is not None:
                # Factor a or a^c from a^b.
                if pull=='right':
                    _c, _d = _d, _c
                if RealPos.readily_includes(base_ns):
                    expr = eq.update(exp_factored_real.instantiate(
                            {a: self.base, b: _b, c: _c, d: _d},
                            replacements=replacements))
                    return eq.relation
                elif RealNonZero.readily_includes(base_ns) and (
                      Integer.readily_includes(exp_ns)):
                    expr = eq.update(exp_factored_int.instantiate(
                            {a: self.base, b: _b, c: _c, d: _d},
                            replacements=replacements))
                    return eq.relation
                else:
                    raise UnsatisfiedPrerequisites(
                            "%s is not readily provable to be a positive "
                            "number, or a nonzero real with %s as an "
                            "integer in order to enable the factorization "
                            "of %s."
                            %(self.base, self.exponent, self))
            
            factor_base = None
            if readily_factorable(expr.base, factor):
                factor_base = factor
            elif isinstance(factor, Exp):
                factor_base = factor.base
            
            if factor_base is None or not (
                    readily_factorable(expr.base, factor_base)):
                raise UnsatisfiedPrerequisites(
                        "%s is not readily factorable from %s"
                        %(factor, self))
            
            # Factor within the base. For example,
            # a = b*c
            # a^d = (b^d) * (c^d) = b^e * b^(e-d) * c^d
            expr = eq.update(expr.inner_expr().base.factorization(
                factor_base, pull=pull, group_factors=True, 
                group_remainder=True, preserve_all=True))
            # distribute: (b^d) * (c^d)
            expr = eq.update(expr.inner_expr().distribution(
                    preserve_all=True))
            num_entries = expr.operands.num_entries()
            idx = 0 if pull=='left' else -1
            if factor==expr.operands[idx]:
                # e.g., a^c factored out of (a*b)^c
                return eq.relation
            # factor portion: (b^e * b^(e-d)) * c^d
            inner_expr = expr.inner_expr().operands[idx]
            expr = eq.update(inner_expr.factorization(
                                factor, pull=pull,
                                group_factors=group_factors, 
                                group_remainder=False, preserve_all=True))
            # disassociate: b^e * b^(e-d) * c^d
            expr = eq.update(expr.disassociation(
                    idx, preserve_all=group_remainder))
            if group_remainder:
                expr = eq.update(expr.association(
                        0 if pull=='right' else -num_entries,
                        num_entries))

        return eq.relation

    @equality_prover('distributed', 'distribute')
    def distribution(self, **defaults_config):
        '''
        Equate this exponential to a form in which the exponent
        is distributed over factors, or a power of a power reduces to
        a power of multiplied exponents.
        Examples:
            (a*b*c)^f = a^f * b^f * c^f
            (a/b)^f = (a^f / b^f)
        '''
        from proveit.numbers import Mult, Div, NaturalPos, RealPos, Real
        import proveit.numbers.exponentiation as exp_pkg
        base = self.base
        exponent = self.exponent
        exp_ns = readily_provable_number_set(exponent, default=Complex)
        if isinstance(base, Mult):
            if self.base.operands.is_double():
                _a, _b = self.base.operands
            else:
                _m = self.base.operands.num_elements()
                _a = self.base.operands
            if NaturalPos.readily_includes(exp_ns):
                if self.base.operands.is_double():
                    return exp_pkg.posnat_power_of_product.instantiate(
                        {a: _a, b: _b, n: exponent})
                else:
                    return exp_pkg.posnat_power_of_products.instantiate(
                        {m: _m, a: _a, n: exponent})
            elif RealPos.readily_includes(exp_ns):
                if self.base.operands.is_double():
                    return exp_pkg.pos_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent})
                else:
                    return exp_pkg.pos_power_of_products.instantiate(
                        {m: _m, a: _a, b: exponent})
            elif Real.readily_includes(exp_ns):
                if self.base.operands.is_double():
                    return exp_pkg.real_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent})
                else:
                    return exp_pkg.real_power_of_products.instantiate(
                        {m: _m, a: _a, b: exponent})
            else:  # Complex is the default
                if self.base.operands.is_double():
                    return exp_pkg.complex_power_of_product.instantiate(
                        {a: _a, b: _b, c: exponent})
                else:
                    return exp_pkg.complex_power_of_products.instantiate(
                        {m: _m, a: _a, b: exponent})
        elif isinstance(base, Div):
            assert self.base.operands.is_double()
            _a, _b = self.base.operands
            if NaturalPos.readily_includes(exp_ns):
                return exp_pkg.posnat_power_of_quotient.instantiate(
                    {a: _a, b: _b, n: exponent})
            else:
                if RealPos.readily_includes(exp_ns):
                    thm = exp_pkg.pos_power_of_quotient
                elif Real.readily_includes(exp_ns):
                    thm = exp_pkg.real_power_of_quotient
                else:  # Complex is the default
                    thm = exp_pkg.complex_power_of_quotient
                return thm.instantiate(
                    {a: _a, b: _b, c: exponent})
        else:
            # Nothing to distribute over.
            return Equals(self, self).conclude_via_reflexivity()

    @equality_prover('double_exponent_reduced', 'double_exponent_reduce')
    def double_exponent_reduction(self, **defaults_config):
        from proveit.numbers import NaturalPos, RealPos, Real
        import proveit.numbers.exponentiation as exp_pkg
        base = self.base
        exponent = self.exponent
        exp_ns = readily_provable_number_set(exponent, default=Complex)
        if not isinstance(base, Exp):
            raise ValueError("'double_exponent_reduction' only applicable "
                             "when the 'base' is an exponential, not for %s"
                             %self)
        base_exp_ns = readily_provable_number_set(
                base.exponent, default=Complex)
        
        _a = base.base
        if NaturalPos.readily_includes(exp_ns):
            if NaturalPos.readily_includes(base_exp_ns):
                _m, _n = base.exponent, exponent
                return exp_pkg.posnat_power_of_posnat_power.instantiate(
                    {a: _a, m: _m, n: _n})
            else:
                _b, _c = base.exponent, exponent
                if RealPos.readily_includes(base_exp_ns):
                    thm = exp_pkg.pos_power_of_pos_power
                elif Real.readily_includes(base_exp_ns):
                    thm = exp_pkg.real_power_of_real_power
                else:  # Complex is the default
                    thm = exp_pkg.complex_power_of_complex_power
                return thm.instantiate(
                    {a: _a, b: _b, c: _c})
        else:
            _b, _c = base.exponent, exponent
            if RealPos.readily_includes(exp_ns) and (
                    RealPos.readily_includes(base_exp_ns)):
                thm = exp_pkg.pos_power_of_pos_power
            elif Real.readily_includes(exp_ns) and (
                    Real.readily_includes(base_exp_ns)):
                thm = exp_pkg.real_power_of_real_power
            else:  # Complex is the default
                thm = exp_pkg.complex_power_of_complex_power
            return thm.instantiate(
                {a: _a, b: _b, c: _c})

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

        # use the Mult.combining_exponents() to deduce equality to self
        exp_separated = mult_equiv.combining_exponents(preserve_all=True)

        replacements = list(defaults.replacements)
        if defaults.auto_simplify:
            with Mult.temporary_simplification_directives() as tmp_directives:
                # Don't recombine the exponents after separating them.
                tmp_directives.combine_all_exponents = False
                tmp_directives.combine_numeric_rational_exponents = False
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
        from proveit.logic import InSet
        import proveit.numbers.exponentiation as exp_pkg

        if number_set == ZeroSet:
            # Prove 0^x in {0}; while we are at it, prove 0^x = 0.
            exp_pkg.exponentiated_zero.instantiate({x:self.exponent})
            return exp_pkg.exp_in_zero_set.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == NaturalPos:
            return exp_pkg.exp_natpos_closure.instantiate(
                {a: self.base, b: self.exponent})
        elif number_set == Natural:
            # Use the NaturalPos closure which applies for
            # any Natural base and exponent.
            self.deduce_in_number_set(NaturalPos)
            return InSet(self, Natural).prove()
        elif number_set == Integer:
            return exp_pkg.exp_int_closure.instantiate(
                {a: self.base, b: self.exponent})
        elif number_set == Rational:
            power_is_nat = InSet(self.exponent, Natural)
            if not power_is_nat.readily_provable():
                # Use the RationalNonZero closure which works
                # for negative exponents as well.
                self.deduce_in_number_set(RationalNonZero)
                return InSet(self, Rational).prove()
            return exp_pkg.exp_rational_closure_nat_power.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == RationalNonZero:
            return exp_pkg.exp_rational_nonzero_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == RationalPos:
            return exp_pkg.exp_rational_pos_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == Real:
            if self.exponent == frac(one, two):
                return exp_pkg.sqrt_real_closure.instantiate({a: self.base})
            else:
                power_is_nat = InSet(self.exponent, Natural)
                if not power_is_nat.readily_provable():
                    # Use the RealPos closure which allows
                    # any real exponent but requires a
                    # non-negative base.
                    self.deduce_in_number_set(RealPos)
                    return InSet(self, Real).prove()
                return exp_pkg.exp_real_closure_nat_power.instantiate(
                        {a: self.base, b: self.exponent})
        elif number_set == RealPos:
            if self.exponent == frac(one, two):
                return exp_pkg.sqrt_real_pos_closure.instantiate(
                        {a: self.base})
            elif self.exponent == two:
                return exp_pkg.sqrd_pos_closure.instantiate({a: self.base})
            else:
                return exp_pkg.exp_real_pos_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == RealNonNeg:
            if self.exponent == frac(one, two):
                return exp_pkg.sqrt_real_non_neg_closure.instantiate({a: self.base})
            elif self.exponent == two:
                return exp_pkg.sqrd_non_neg_closure.instantiate({a: self.base})
            else:
                return exp_pkg.exp_real_non_neg_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == Complex:
            if self.exponent == frac(one, two):
                return exp_pkg.sqrt_complex_closure.instantiate(
                    {a: self.base})
            else:
                return exp_pkg.exp_complex_closure.instantiate(
                    {a: self.base, b: self.exponent})
        elif number_set == ComplexNonZero:
            return exp_pkg.exp_complex_nonzero_closure.instantiate(
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
            if (greater(_a_sub, zero).readily_provable() and
                greater_eq(_x_sub, zero).readily_provable()):
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
            elif (greater_eq(_a_sub, zero).readily_provable() and
                greater(_x_sub, zero).readily_provable()):
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
            elif (Less(_a_sub, zero).readily_provable() and
                greater(_x_sub, zero).readily_provable()):
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
            elif (LessEq(_a_sub, zero).readily_provable() and
                greater(_x_sub, zero).readily_provable()):
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
                Less(_y_sub, zero).readily_provable()):
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
            if (greater(_a_sub, one).readily_provable() and
                InSet(_x_sub, Real).readily_provable()):
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

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        base_ns = readily_provable_number_set(self.base, default=Complex)
        exp_ns = readily_provable_number_set(self.exponent, default=Complex)
        if base_ns == ZeroSet and RealPos.readily_includes(exp_ns):
            # 0^x = 0 for x > 0.
            return ZeroSet
        if self.exponent==two:
            # Squaring is handled as a special case, but we should
            # extend this to all ven powers.
            if IntegerNonZero.readily_includes(base_ns):
                return NaturalPos
            if Integer.readily_includes(base_ns):
                return Natural
            if RationalNonZero.readily_includes(base_ns):
                return RationalPos
            if Rational.readily_includes(base_ns):
                return RationalNonNeg
            if RealNonZero.readily_includes(base_ns):
                return RealPos
            if Real.readily_includes(base_ns):
                return RealNonNeg
        if Natural.readily_includes(base_ns) and (
                Natural.readily_includes(exp_ns)):
            return NaturalPos
        if Integer.readily_includes(base_ns) and (
                Natural.readily_includes(exp_ns)):
            return Integer
        if RationalPos.readily_includes(base_ns) and (
                Integer.readily_includes(exp_ns)):
            return RationalPos
        if (RationalNonZero.readily_includes(base_ns)
                and Integer.readily_includes(exp_ns)):
            return RationalNonZero
        if Rational.readily_includes(base_ns) and (
                Natural.readily_includes(exp_ns)):
            return Rational
        if RealPos.readily_includes(base_ns) and Real.readily_includes(exp_ns):
            return RealPos
        if RealNonNeg.readily_includes(base_ns) and (
                Real.readily_includes(exp_ns)):
            return RealNonNeg
        if Real.readily_includes(base_ns) and Natural.readily_includes(exp_ns):
            return Real
        if ComplexNonZero.readily_includes(base_ns):
            return ComplexNonZero
        return Complex


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
        from proveit.numbers import zero, is_numeric_int, DIGITS
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
        if is_numeric_int(exponent):
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
