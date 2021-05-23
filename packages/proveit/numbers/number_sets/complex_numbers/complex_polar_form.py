from proveit import Judgment, defaults, ProofFailure
from proveit import r, theta

def complex_polar_coordinates(expr, *, radius_must_be_nonneg=True,
                              nonneg_radius_preferred=True,
                              do_include_unit_length_reduction=True,
                              reductions=None):
    '''
    Given an expression, expr, of the complex number polar form,
        r * exp(i * theta),
    or something obviously equivalent to this, where r and theta are 
    Real (and r is preferably RealNonNeg) under the given assumptions, 
    return
        (r, theta)
    as a tuple pair. If defaults.automation=False, the r and theta must
    already be known to be RealNonNeg and Real respectively. If
    defaults.automation=True, we may attempt to prove these through 
    automation.
    
    If radius_must_be_nonneg and nonneg_radius_preferred are False, 
    we won't worry about ensuring that r is non-negative (so the result
    can be ambiguous).  If radius_must_be_nonneg is True, a ValueError
    will be raised if we can't convert to a form where r is known to be
    non-negative.
    
    If expr is not exactly in this complex number polar form and
    'reductions' is provided as a set, add to the 'reductions' set
    an equation that equates the exact form on the left with the
    original form on the right.  This may be useful to use as
    'reductions' in instantiations of theorems that employ the
    complex number polar form so it may perform proper reductions
    to the desired form.  For example, if expr=5 is provided,
    the added reduction will be
        5 * exp(i * 0) = 5.
    
    If do_include_unit_length_reduction is True,  we will included
    reductions so that it will reduce from the unit length
    form as well.  For example, if expr=1 is provided, the added
    reductions will be
        exp(i * 0) = 1
        1 * 1 = 1.
    This also works in a way that cascades when reducing from the
    general polar form:
        1 * exp(i * 0) = 1 * 1 = 1
    
    Raise ValueError if the expr is not obviously equivalent to a
    complex number polar form.

    Also see unit_length_complex_polar_angle.
    '''
    from . import complex_polar_negation, complex_polar_radius_negation
    from proveit.logic import InSet, Equals
    from proveit.numbers import zero, one, e, i, pi, Real, RealNonNeg, Complex
    from proveit.numbers import Add, LessEq, Neg, Mult, Exp
    orig_expr = expr
    automation = defaults.automation
    simplify = defaults.auto_simplify
    if reductions is None: reductions = set()

    def add_reduction(reduction, _radius, _theta):
        '''
        Add the given reduction.  First check that its left and
        rights sides are as expected: the left should be the polar
        form and the right should be the original expression.
        '''
        polar_form = Mult(_radius, Exp(e, Mult(i, _theta)))
        assert (isinstance(reduction, Judgment) 
                and isinstance(reduction.expr, Equals) 
                and reduction.lhs == polar_form
                and reduction.rhs == orig_expr), (
                        "Reduction, %s, not a judgement "
                        "for %s = %s"%(reduction, polar_form, orig_expr))
        if do_include_unit_length_reduction and _radius == one:
            # As a unit length complex number, let's include the
            # reduction from the unit length form in case a unit length 
            # formula is applied (cover the bases).
            # The 'automation' allowed here is negligible (assuming
            # we have already proven appropriate set membership by this
            # point).
            reductions.add(reduction.inner_expr().lhs.eliminate_one(
                    0, automation=True))
            # But prepare for a multi-stage reduction:
            # 1 * exp[i * theta] = 1 * orig_expr = orig_expr
            reductions.add(Mult(one, orig_expr).one_elimination(
                    0, automation=True))
        elif reduction.lhs != reduction.rhs:
            reductions.add(reduction)
    def raise_not_valid_form(extra_msg=None):
        if extra_msg is None: extra_msg = ""
        raise ValueError("%s not in a form that is obviously "
                         "reducible from an r * exp(i*theta) form. %s"
                         %(orig_expr, extra_msg))
    
    if isinstance(expr, Neg):
        # expr = -(r*exp(i*theta0)) = r*exp(i*(theta0 + pi))
        inner_reductions = set()
        # obtain the theta of the negated expression.
        _r, _theta0 = complex_polar_coordinates(
                expr.operand, radius_must_be_nonneg=radius_must_be_nonneg,
                nonneg_radius_preferred=nonneg_radius_preferred,
                reductions=inner_reductions)
        # theta = theta0 + pi
        _theta = Add(_theta0, pi)
        if defaults.auto_simplify:
            # simplify theta
            theta_simplification = _theta.simplification()
            inner_reductions.add(theta_simplification)
            _theta = theta_simplification.rhs
        # Allow these automation which should be trivial.
        InSet(Mult(i, _theta), Complex).prove(automation=True)
        InSet(Exp(e, Mult(i, _theta)), Complex).prove(automation=True)
        # reduction: r*exp(i*theta) = orig_expr [via -(r*exp(i*theta0))]
        reduction = complex_polar_negation.instantiate(
                {r:_r, theta:_theta0}, replacements=inner_reductions,
                auto_simplify=False)
        # Add the reduction and return the coordinates.
        add_reduction(reduction, _r, _theta)
        return (_r, _theta)
    elif isinstance(expr, Exp):
        # exp(i * theta) reduced from 1 * exp(i * theta).
        inner_reductions = set()
        _theta = unit_length_complex_polar_angle(
                expr, reductions=inner_reductions)
        # Allow these automation which should be trivial.
        InSet(Mult(i, _theta), Complex).prove(automation=True)
        InSet(Exp(e, Mult(i, _theta)), Complex).prove(automation=True)
        _r = one
        expr = Mult(_r, Exp(e, Mult(i, _theta)))
        # reduction: 1*exp(i * theta) = exp(i * theta)
        reduction = expr.one_elimination(0, auto_simplify=False)
        # reduction: 1*exp(i * theta) = orig_expr
        if len(inner_reductions) > 0:
            reduction = reduction.inner_expr().rhs.substitute(
                    inner_reductions.pop().rhs)
        # Add the reduction and return the coordinates.
        add_reduction(reduction, _r, _theta)
        return (_r, _theta)
    
    # Search for an exponentiation factor with base of 'e' and an 
    # imaginary number in the exponent.
    complex_exp_factor_idx = None
    if isinstance(expr, Mult):
        i_factor_idx = None
        for idx, factor in enumerate(expr.factors):
            if isinstance(factor, Exp) and factor.base == e:
                # exp(x) type factor; check for imaginary number in 
                # exponent.
                contains_imaginary_factor = False
                sub_expr = factor.exponent
                if isinstance(sub_expr, Neg):
                    sub_expr = sub_expr.operand
                if isinstance(sub_expr, Mult):
                    if i in sub_expr.operands.entries:
                        contains_imaginary_factor = True
                else:
                    contains_imaginary_factor = (sub_expr == i)
                if contains_imaginary_factor:
                    # Found imaginary number in an exponent.
                    if ((complex_exp_factor_idx is not None) or
                            (i_factor_idx is not None)):
                        # We already have an imaginary number in
                        # an exponent.  We can only have one.
                        raise_not_valid_form()
                    complex_exp_factor_idx = idx
    if complex_exp_factor_idx is None:
        # No exp(i theta) factor.  Let's multiply by exp(i * 0).
        exp_i0 = Exp(e, Mult(i, zero))
        expr = Mult(expr, exp_i0)
        inner_reductions = set()
        _r, _theta = complex_polar_coordinates(
                expr, radius_must_be_nonneg=radius_must_be_nonneg,
                nonneg_radius_preferred=nonneg_radius_preferred,
                do_include_unit_length_reduction=False,
                reductions=inner_reductions)
        assert _theta == zero
        # Allow this automation which should be trivial.
        InSet(exp_i0, Complex).prove(automation=True)
        # reduction: r * exp(i * theta) = orig_expr * exp(i * 0)
        if len(inner_reductions) > 0:
            reduction = inner_reductions.pop()
        else:
            reduction = Equals(expr, expr).conclude_via_reflexivity()
        # reduction: r * exp(i * theta) = orig_expr
        reduction = reduction.inner_expr().rhs.simplify(
                preserve_expr=orig_expr)        
        add_reduction(reduction, _r, _theta)
        return (_r, _theta)
    
    # expr in ... * exp(... * i * ...) * ... form
    # Obtain the theta from exp(... * i * ...) = exp[i * theta0].
    inner_reductions = set()
    _theta0 = unit_length_complex_polar_angle(
            expr.factors[complex_exp_factor_idx], 
            reductions=inner_reductions)
    expr = Mult(*expr.factors.entries[:complex_exp_factor_idx], 
                Exp(e, Mult(i, _theta0)),
                *expr.factors.entries[complex_exp_factor_idx+1:])
    # reduction: ... * expr[i * theta0] * ... = orig_expr
    if len(inner_reductions) > 0:
        reduction = expr.inner_expr().operands[1].substitution(
                inner_reductions.pop().rhs)
    else:
        reduction = Equals(expr, expr).conclude_via_reflexivity()
    if not expr.operands.is_double() or complex_exp_factor_idx != 1:
        # Pull the exp(i*theta) type factor to the right.
        # reduction: r0 * exp(i * theta0) = orig_expr
        reduction = reduction.inner_expr().lhs.factor(
                complex_exp_factor_idx, pull='right',
                group_remainder=True, auto_simplify=False)
        expr = reduction.lhs
    # expr: r0 * exp(i * theta0)
    assert expr.operands.is_double() and isinstance(expr.operands[1], Exp)
    # Check that r0 is real and that we know it's relation with zero.
    _r0 = expr.operands[0]
    if (not automation and isinstance(_r0, Mult) and
            all(InSet(factor, RealNonNeg).proven() for 
                factor in _r0.factors)):
        # We'll allow this low-level automation to
        # prove r0 is non-negative given its factors are non-negative.
        InSet(_r0, RealNonNeg).prove()    
    elif (not automation and isinstance(_r0, Mult) and
            all(InSet(factor, Real).proven() for 
                factor in _r0.factors)):
        # We'll allow this low-level automation to
        # prove r0 is real given its factors are real.
        InSet(_r0, Real).prove()    
    else:
        try:
            InSet(_r0, Real).prove()
        except ProofFailure:
            raise_not_valid_form("%s not known to be real."%_r0)
    if radius_must_be_nonneg:
        # We must know the relationship between r0 and 0 so we
        # can ensure r is non-negative.
        if not nonneg_radius_preferred:
            ValueError("nonneg_radius_preferred must be True if "
                       "radius_must_be_nonneg is True.")
        try:
            radius_relation_with_zero = LessEq.sort([zero, _r0])
        except ProofFailure:
            raise_not_valid_form("Relation of %s to 0 is unknown and "
                                 "radius_must_be_nonneg is True."%_r0)
    elif nonneg_radius_preferred:
        # We would prefer to know the relationship between r0 and 0
        # for r to be non-negative as preferred.
        try:
            radius_relation_with_zero = LessEq.sort([zero, _r0])
        except ProofFailure:
            # To bad so sad.  We can't do it, it wasn't demanded,
            # so forget it.
            nonneg_radius_preferred = False
    # Is r0 <= 0?
    if (nonneg_radius_preferred and
            radius_relation_with_zero.normal_rhs == zero):
        # r0 <= 0, so we must negate it and add pi to the angle.
        inner_reductions = {reduction}
        # theta: theta + pi
        _theta = Add(_theta0, pi)
        if simplify:
            # simplify theta
            theta_simplification = _theta.simplification()
            inner_reductions.add(theta_simplification)
            _theta = theta_simplification.rhs
        # r: -r0
        _r = Neg(_r0)
        if simplify:
            # simplify radius
            radius_simplification = _r.simplification()
            inner_reductions.add(radius_simplification)
            _r = radius_simplification.rhs
        # reduction: r*exp(i*theta) = orig_expr [via r0*exp(i*theta0))]
        reduction = complex_polar_radius_negation.instantiate(
                {r:_r0, theta:_theta0}, replacements=inner_reductions,
                auto_simplify=False)
    else:
        _r, _theta = _r0, _theta0
    if nonneg_radius_preferred:
        # We know that r is real and r >= 0, 
        # so r in RealNonNeg should be trivial.
        InSet(_r, RealNonNeg).prove()
    # Add the reduction and return the coordinates.
    add_reduction(reduction, _r, _theta)
    return (_r, _theta)

def unit_length_complex_polar_angle(expr, *, reductions=None):
    '''
    Given an expression, expr, of the complex number polar form,
        exp(i * theta),
    or something obviously equivalent to this, where r is RealNonNeg 
    and theta is Real under the given assumptions, return theta.
    If defaults.automation=False, theta must already be known to be 
    Real. If defaults.automation=True, we may attempt to prove these 
    through automation.
    
    If expr is not exactly in this complex number polar form and
    'reductions' is provided as a set, add to the 'reductions' set
    an equation that equates the exact form on the left with the
    original form on the right.  This may be useful to use as
    'replacements' in instantiations of theorems that employ the
    complex number polar form so it may perform proper reductions
    to the desired form.  For example, if expr=1 is provided,
    the added reduction will be
        exp(i * 0) = 1
    
    Raise ValueError if the expr is not obviously equivalent to a
    complex number polar form.
    
    Also see complex_polar_coordinates.
    '''
    from proveit import ExprRange
    from proveit.logic import Equals, InSet
    from proveit.numbers import zero, one, e, i, pi
    from proveit.numbers import Add, Neg, Mult, Exp, Real
    from . import unit_length_complex_polar_negation
    if reductions is None: reductions = set()

    def raise_not_valid_form():
        raise ValueError("%s not in a form that is obviously "
                         "reducible from an exp(i*theta) form. ")
    orig_expr = expr
    automation = defaults.automation
    simplify = defaults.auto_simplify
    def add_reduction(reduction, _theta):
        '''
        Add the given reduction.  First check that its left and
        rights sides are as expected: the left should be the polar
        form and the right should be the original expression.
        '''
        polar_form = Exp(e, Mult(i, _theta))
        assert (isinstance(reduction, Judgment)
                and isinstance(reduction.expr, Equals)
                and reduction.lhs == polar_form
                and reduction.rhs == orig_expr)
        if reduction.lhs != reduction.rhs:
            reductions.add(reduction)

    if expr == one:
        # expr = 1 = exp(i * 0)
        _theta = zero
        expr = Exp(e, Mult(i, _theta))
        # reduction: exp(i * 0) = 1
        reduction = expr.simplification()
        # Add the reduction and return theta.
        add_reduction(reduction, _theta)
        return _theta
    if isinstance(expr, Exp) and expr.base == e:
        if expr.exponent == i:
            # expr = exp(i) = exp(i * 1)
            theta = one
            expr = Exp(e, Mult(i, one))
            # reduction: exp(i * 1) = exp(i)
            reduction = expr.inner_expr().exponent.one_elimination(1)
            # Add the reduction and return theta.
            add_reduction(reduction, _theta)
            return _theta
        if hasattr(expr.exponent, 'factorization'):
            if (isinstance(expr.exponent, Mult) and 
                    expr.exponent.operands.is_double()
                    and expr.exponent.operands[0] == i):
                # Already in the proper form.  No reduction needed,
                # but we do need to check that theta is real.
                _theta = expr.exponent.factors[1]
                InSet(_theta, Real).prove()
                return _theta
            try:
                # Factor i in the exponent, pulling to the left to
                # get into exp(i * theta) form.
                factorization = expr.inner_expr().exponent.factorization(
                        i, pull='left', group_remainder=True)
                expr = factorization.rhs
                assert isinstance(expr.exponent, Mult)
                assert expr.exponent.factors.is_double()
                assert expr.exponent.factors[0] == i
                _theta = expr.exponent.factors[1]
                if (not automation and isinstance(_theta, Neg) and 
                        InSet(_theta.operand, Real).proven()):
                    # We'll allow this low-level automation to
                    # prove -theta is real given theta is real.
                    InSet(_theta, Real).prove(automation=True)
                elif (not automation and isinstance(_theta, Mult) and 
                        all(InSet(Mult(factor), Real).proven() if
                            isinstance(factor, ExprRange) else
                            InSet(factor, Real).proven() for
                            factor in _theta.factors)):
                    # We'll allow this low-level automation to
                    # prove a product is real given that the factors
                    # are known to be real.
                    InSet(_theta, Real).prove(automation=True)                    
                else:
                    InSet(_theta, Real).prove()
                # reduction: exp(i * theta) = orig_expr
                reduction = factorization.derive_reversed()
                # Add the reduction and return theta.
                add_reduction(reduction, _theta)
                return _theta
            except ValueError:
                raise_not_valid_form()
    if isinstance(expr, Neg):
        # expr = -exp(i*theta0) = exp(i*(theta0 + pi)) = exp(i*theta)
        inner_reductions = set()
        # obtain the theta of the negated expression.
        _theta0 = unit_length_complex_polar_angle(
                expr.operand, reductions=inner_reductions)
        # theta = theta0 + pi
        _theta = Add(_theta0, pi)
        if simplify:
            # simplify theta
            theta_simplification = _theta.simplification()
            inner_reductions.add(theta_simplification)
            _theta = theta_simplification.rhs
        # reduction: exp(i*theta) = orig_expr [via -exp(i*theta0)]
        reduction = unit_length_complex_polar_negation.instantiate(
                {theta:_theta0}, replacements=inner_reductions,
                auto_simplify=False)
        # Add the reduction and return theta.
        add_reduction(reduction, _theta)
        return theta
        
    raise_not_valid_form()
