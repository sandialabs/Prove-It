from proveit import Judgment, USE_DEFAULTS, ProofFailure
from proveit import r, theta

def complex_polar_coordinates(expr, *, assumptions=USE_DEFAULTS,
                              automation=False, simplify=True,
                              radius_must_be_nonneg=True,
                              nonneg_radius_preferred=True,
                              reductions=None):
    '''
    Given an expression, expr, of the complex number polar form,
        r * exp(i * theta),
    or something obviously equivalent to this, where r and theta are 
    Real (and r is preferably RealNonNeg) under the given assumptions, 
    return
        (r, theta)
    as a tuple pair. If automation=False, the r and theta must
    already be known to be RealNonNeg and Real respectively. If
    automation=True, we may attempt to prove these through automation.
    
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
    to the desired form.  For example, if expr=1 is provided,
    the added reduction will be
        1 * exp(i * 0) = 1
    
    Raise ValueError if the expr is not obviously equivalent to a
    complex number polar form.

    Also see unit_length_complex_polar_angle.
    '''
    from proveit.trigonometry import (
            complex_polar_negation, complex_polar_radius_negation)
    from proveit.logic import InSet, Equals
    from proveit.numbers import zero, one, e, i, pi, Real, RealNonNeg
    from proveit.numbers import Add, LessEq, Neg, Mult, Exp
    orig_expr = expr

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
                and reduction.rhs == orig_expr)
        if reductions is not None:
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
                expr.operand, assumptions=assumptions, 
                automation=automation, simplify=simplify,
                radius_must_be_nonneg=radius_must_be_nonneg,
                nonneg_radius_preferred=nonneg_radius_preferred,
                reductions=inner_reductions)
        # theta = theta0 + pi
        _theta = Add(_theta0, pi)
        if simplify:
            # simplify theta
            theta_simplification = _theta.simplification(
                    assumptions=assumptions)
            inner_reductions.add(theta_simplification)
            _theta = theta_simplification.rhs
        # reduction: r*exp(i*theta) = orig_expr [via -(r*exp(i*theta0))]
        reduction = complex_polar_negation.instantiate(
                {r:_r, theta:_theta0}, reductions=inner_reductions,
                assumptions=assumptions)
        # Add the reduction and return the coordinates.
        add_reduction(reduction, _r, _theta)
        return (_r, _theta)
    elif isinstance(expr, Exp):
        # exp(i * theta) reduced from 1 * exp(i * theta).
        inner_reductions = set()
        _theta = unit_length_complex_polar_angle(
                expr, assumptions=assumptions, 
                automation=automation, simplify=simplify, 
                reductions=inner_reductions)
        _r = one
        expr = Mult(_r, Exp(e, Mult(i, _theta)))
        # reduction: 1*exp(i * theta) = exp(i * theta)
        reduction = expr.one_elimination(0, assumptions)
        # reduction: 1*exp(i * theta) = orig_expr
        if len(inner_reductions) > 0:
            reduction = reduction.inner_expr().rhs.substitute(
                    inner_reductions.pop())
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
                expr, assumptions=assumptions, 
                automation=automation, simplify=simplify,
                radius_must_be_nonneg=radius_must_be_nonneg,
                nonneg_radius_preferred=nonneg_radius_preferred,
                reductions=inner_reductions)
        # reduction: r * exp(i * theta) = orig_expr * exp(i * 0)
        if len(inner_reductions) > 0:
            reduction = inner_reductions.pop()
        else:
            reduction = Equals(expr, expr).prove(assumptions)
        # reduction: r * exp(i * theta) = orig_expr * 1
        reduction = reduction.inner_expr().rhs.operands[1].simplify(
                assumptions)
        # reduction: r * exp(i * theta) = orig_expr
        reduction = reduction.inner_expr().rhs.eliminate_one(
                1, assumptions)
        add_reduction(reduction, _r, _theta)
        return (_r, _theta)
    
    # expr in ... * exp(... * i * ...) * ... form
    # Obtain the theta from exp(... * i * ...) = exp[i * theta0].
    inner_reductions = set()
    _theta0 = unit_length_complex_polar_angle(
            expr.factors[complex_exp_factor_idx], 
            assumptions=assumptions, automation=automation, 
            simplify=simplify, reductions=inner_reductions)
    expr = Mult(*expr.factors.entries[:complex_exp_factor_idx], 
                Exp(e, Mult(i, _theta0)),
                *expr.factors.entries[complex_exp_factor_idx+1:])
    # reduction: ... * expr[i * theta0] * ... = orig_expr
    if len(inner_reductions) > 0:
        reduction = expr.inner_expr().operands[1].substitution(
                inner_reductions.pop().rhs, assumptions=assumptions)
    else:
        reduction = Equals(expr, expr).prove(assumptions=assumptions)
    if not expr.operands.is_double() or complex_exp_factor_idx != 1:
        # Pull the exp(i*theta) type factor to the right.
        # reduction: r0 * exp(i * theta0) = orig_expr
        reduction = reduction.inner_expr().lhs.factor(
                complex_exp_factor_idx, pull='right',
                group_remainder=True, assumptions=assumptions)
        expr = reduction.lhs
    # expr: r0 * exp(i * theta0)
    assert expr.operands.is_double() and isinstance(expr.operands[1], Exp)
    # Check that r0 is real and that we know it's relation with zero.
    _r0 = expr.operands[0]
    if (not automation and isinstance(_r0, Mult) and
            all(InSet(factor, RealNonNeg).proven(assumptions) for 
                factor in _r0.factors)):
        # We'll allow this low-level automation to
        # prove r0 is non-negative given its factors are non-negative.
        InSet(_r0, RealNonNeg).prove(assumptions)    
    elif (not automation and isinstance(_r0, Mult) and
            all(InSet(factor, Real).proven(assumptions) for 
                factor in _r0.factors)):
        # We'll allow this low-level automation to
        # prove r0 is real given its factors are real.
        InSet(_r0, Real).prove(assumptions)    
    else:
        try:
            InSet(_r0, Real).prove(assumptions, automation=automation)
        except ProofFailure:
            raise_not_valid_form("%s not known to be real."%_r0)
    if radius_must_be_nonneg:
        # We must know the relationship between r0 and 0 so we
        # can ensure r is non-negative.
        if not nonneg_radius_preferred:
            ValueError("nonneg_radius_preferred must be True if "
                       "radius_must_be_nonneg is True.")
        try:
            radius_relation_with_zero = LessEq.sort([zero, _r0],
                                                    assumptions=assumptions)
        except ProofFailure:
            raise_not_valid_form("Relation of %s to 0 is unknown."%_r0)
    elif nonneg_radius_preferred:
        # We would prefer to know the relationship between r0 and 0
        # for r to be non-negative as preferred.
        try:
            radius_relation_with_zero = LessEq.sort([zero, _r0],
                                                    assumptions=assumptions)
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
            theta_simplification = _theta.simplification(
                    assumptions=assumptions)
            inner_reductions.add(theta_simplification)
            _theta = theta_simplification.rhs
        # r: -r0
        _r = Neg(_r0)
        if simplify:
            # simplify radius
            radius_simplification = _r.simplification(
                    assumptions=assumptions)
            inner_reductions.add(radius_simplification)
            _r = radius_simplification.rhs
        # reduction: r*exp(i*theta) = orig_expr [via r0*exp(i*theta0))]
        reduction = complex_polar_radius_negation.instantiate(
                {r:_r0, theta:_theta0}, reductions=inner_reductions,
                assumptions=assumptions)
    else:
        _r, _theta = _r0, _theta0
    if nonneg_radius_preferred:
        # We know that r is real and r >= 0, 
        # so r in RealNonNeg should be trivial.
        InSet(_r, RealNonNeg).prove(assumptions)
    # Add the reduction and return the coordinates.
    add_reduction(reduction, _r, _theta)
    return (_r, _theta)

def unit_length_complex_polar_angle(expr, *, assumptions=USE_DEFAULTS,
                                    automation=False, simplify=True,
                                    reductions=None):
    '''
    Given an expression, expr, of the complex number polar form,
        exp(i * theta),
    or something obviously equivalent to this, where r is RealNonNeg 
    and theta is Real under the given assumptions, return theta.
    If automation=False, theta must already be known to be Real. If
    automation=True, we may attempt to prove these through automation.
    
    If expr is not exactly in this complex number polar form and
    'reductions' is provided as a set, add to the 'reductions' set
    an equation that equates the exact form on the left with the
    original form on the right.  This may be useful to use as
    'reductions' in instantiations of theorems that employ the
    complex number polar form so it may perform proper reductions
    to the desired form.  For example, if expr=1 is provided,
    the added reduction will be
        exp(i * 0) = 1
    
    Raise ValueError if the expr is not obviously equivalent to a
    complex number polar form.
    
    Also see complex_polar_coordinates.
    '''
    from proveit.logic import Equals, InSet
    from proveit.numbers import zero, one, e, i, pi
    from proveit.numbers import Add, Neg, Mult, Exp, Real
    from proveit.trigonometry import (
            unit_length_complex_polar_negation)
    def raise_not_valid_form():
        raise ValueError("%s not in a form that is obviously "
                         "reducible from an exp(i*theta) form. ")
    orig_expr = expr
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
        if reductions is not None:
            reductions.add(reduction)
    if expr == one:
        # expr = 1 = exp(i * 0)
        _theta = zero
        expr = Exp(e, Mult(i, _theta))
        # reduction: exp(i * 0) = 1
        reduction = expr.simplification(assumptions=assumptions)
        # Add the reduction and return theta.
        add_reduction(reduction, _theta)
        return _theta
    if isinstance(expr, Exp) and expr.base == e:
        if expr.exponent == i:
            # expr = exp(i) = exp(i * 1)
            theta = one
            expr = Exp(e, Mult(i, one))
            # reduction: exp(i * 1) = exp(i)
            reduction = expr.inner_expr().exponent.one_elimination(
                    1, assumptions)
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
                InSet(_theta, Real).prove(
                        assumptions=assumptions, automation=automation)
                return _theta
            try:
                # Factor i in the exponent, pulling to the left to
                # get into exp(i * theta) form.
                factorization = expr.inner_expr().exponent.factorization(
                        i, pull='left', group_remainder=True,
                        assumptions=assumptions)
                expr = factorization.rhs
                assert isinstance(expr.exponent, Mult)
                assert expr.exponent.factors.is_double()
                assert expr.exponent.factors[0] == i
                _theta = expr.exponent.factors[1]
                if (not automation and isinstance(_theta, Neg) and 
                        InSet(_theta.operand, Real).proven(assumptions)):
                    # We'll allow this low-level automation to
                    # prove -theta is real given theta is real.
                    InSet(_theta, Real).prove(
                            assumptions=assumptions, automation=True)     
                else:
                    InSet(_theta, Real).prove(
                        assumptions=assumptions, automation=automation)
                # reduction: exp(i * theta) = orig_expr
                reduction = factorization.derive_reversed(assumptions)
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
                expr.operand, assumptions=assumptions, 
                automation=automation, simplify=simplify, 
                reductions=inner_reductions)
        # theta = theta0 + pi
        _theta = Add(_theta0, pi)
        if simplify:
            # simplify theta
            theta_simplification = _theta.simplification(
                    assumptions=assumptions)
            inner_reductions.add(theta_simplification)
            _theta = theta_simplification.rhs
        # reduction: exp(i*theta) = orig_expr [via -exp(i*theta0)]
        reduction = unit_length_complex_polar_negation.instantiate(
                {theta:_theta0}, reductions=inner_reductions,
                assumptions=assumptions)
        # Add the reduction and return theta.
        add_reduction(reduction, _theta)
        return theta
        
    raise_not_valid_form()
