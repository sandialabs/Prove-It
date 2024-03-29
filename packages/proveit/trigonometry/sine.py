from proveit import Function, Literal, USE_DEFAULTS, prover, relation_prover, equality_prover
from proveit import theta
from proveit.logic import InSet
from proveit.numbers import (
        Real, RealPos, RealNeg, RealNonNeg, RealNonPos, Complex)
from proveit.numbers import Abs, readily_provable_number_set

class Sin(Function):
    # operator of the Sin operation.
    _operator_ = Literal(string_format='sin', theory=__file__)
    
    def __init__(self, angle, *, styles=None):
        Function.__init__(self, Sin._operator_, angle, styles=styles)
        self.angle = angle
    
    def latex(self, **kwargs):
        return r'\sin{' + self.operand.latex(fence=True) + r'}'

    @prover
    def deduce_in_interval(self, **defaults_config):
        '''
        Bound the interval of the Sin function evaluation depending
        upon what is known about the angle.
        '''
        from . import (sine_interval, sine_nonneg_interval,
                       sine_pos_interval, sine_nonpos_interval,
                       sine_neg_interval)
        from proveit.numbers import (zero, pi, Less, LessEq, Neg)
        _theta = self.angle
        if (Less(zero, _theta).readily_provable() and
                Less(_theta, pi).readily_provable()):
            return sine_pos_interval.instantiate({theta:_theta})
        elif (LessEq(zero, _theta).readily_provable() and
                LessEq(_theta, pi).readily_provable()):
            return sine_nonneg_interval.instantiate(
                    {theta:_theta})
        elif (Less(Neg(pi), _theta).readily_provable() and
                Less(_theta, zero).readily_provable()):
            return sine_neg_interval.instantiate(
                    {theta:_theta})
        elif (LessEq(Neg(pi), _theta).readily_provable() and
                LessEq(_theta, zero).readily_provable()):
            return sine_nonpos_interval.instantiate(
                    {theta:_theta})
        else:
            # Without knowing more, we can only bound it by +/-1.
            return sine_interval.instantiate(
                    {theta:_theta})

    @prover
    def deduce_linear_bound(self, **defaults_config):
        '''
        Bound the Sin function evaluation by a line.
        This method remains here temporarily for backward compatibility,
        but has generally been replaced with more detailed, functional
        methods below:
        deduce_linear_lower_bound()
        deduce_linear_upper_bound()
        '''
        from . import (sine_linear_bound, sine_linear_bound_nonneg,
                       sine_linear_bound_nonpos)

        angle_ns = readily_provable_number_set(self.angle, default=Complex)

        if isinstance(self.angle, Abs):
            bound = sine_linear_bound.instantiate(
                    {theta: self.angle.operand})
        elif RealNonNeg.readily_includes(angle_ns):
            bound = sine_linear_bound_nonneg.instantiate(
                    {theta: self.angle})
        elif RealNonPos.readily_includes(angle_ns):
            bound = sine_linear_bound_nonpos.instantiate(
                    {theta: self.angle})
        else:
            _theta = Abs(self.angle)
            bound = sine_linear_bound.instantiate(
                    {theta: _theta})
        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        from proveit.numbers import readily_provable_number_set, Complex
        from proveit.numbers import (zero, one, pi, Less, LessEq, Neg,
                                     IntervalCC, IntervalOC, IntervalCO)
        _theta = self.angle
        theta_ns = readily_provable_number_set(_theta)
        if theta_ns is None: return None
        if not Real.readily_includes(theta_ns): return Complex
        if (Less(zero, _theta).readily_provable() and
                Less(_theta, pi).readily_provable()):
            return IntervalOC(zero, one)
        elif (LessEq(zero, _theta).readily_provable() and
                LessEq(_theta, pi).readily_provable()):
            return IntervalCC(zero, one)
        elif (Less(Neg(pi), _theta).readily_provable() and
                Less(_theta, zero).readily_provable()):
            return IntervalCO(Neg(one), zero)
        elif (LessEq(Neg(pi), _theta).readily_provable() and
                LessEq(_theta, zero).readily_provable()):
            return IntervalCC(Neg(one), zero)
        else:
            # Without knowing more, we can only bound it by +/-1.
            return IntervalCC(Neg(one), one) 

    @prover
    def deduce_linear_lower_bound(self, **defaults_config):
        '''
        Establish a lower bound of the Sin(theta) function evaluation
        by one of two possible linear functions and either strict
        or relaxed bound:
        Sin(theta) > theta         or Sin(theta) >= theta or
        Sin(theta) > (2/pi)(theta) or Sin(theta) >= (2/pi)(theta),
        depending on the domain of the angle theta.
        '''

        if isinstance(self.angle, Abs):
            # for sin|theta|, try the chord y = (2/pi)|theta|,
            # but works only for |theta| <= Pi/2
            from . import sine_linear_bound
            bound = sine_linear_bound.instantiate(
                    {theta: self.angle.operand})
        elif InSet(self.angle, RealNeg).readily_provable():
            # for theta < 0, use the line y = theta
            from . import sine_linear_bound_by_arg_neg
            bound = sine_linear_bound_by_arg_neg.instantiate(
                    {theta: self.angle})
        elif InSet(self.angle, RealNonNeg).readily_provable():
            # for theta >= 0, try the chord y = (2/pi)|theta|,
            # but works only for 0 <= theta <= Pi/2
            from . import sine_linear_bound_nonneg
            bound = sine_linear_bound_nonneg.instantiate(
                    {theta: self.angle})
        elif InSet(self.angle, RealNonPos).readily_provable():
            # for theta <= 0 use the line y = theta
            from . import sine_linear_bound_by_arg_nonpos
            bound = sine_linear_bound_by_arg_nonpos.instantiate(
                    {theta: self.angle})
        else: # not clear what this then does
            from . import sine_linear_bound
            _theta = Abs(self.angle)
            bound = sine_linear_bound.instantiate(
                    {theta: _theta})
        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound

    @prover
    def deduce_linear_upper_bound(self, **defaults_config):
        '''
        Establish an upper bound of the Sin(angle) function evaluation
        by one of two possible linear functions and either strict
        or relaxed bound:
        Sin(theta) < theta         or Sin(theta) <= theta or
        Sin(theta) < (2/pi)(theta) or Sin(theta) <= (2/pi)(theta),
        depending on the domain of the angle theta.
        '''

        if isinstance(self.angle, Abs):
            # for all sin|theta|, use the line y = |theta|
            from . import sine_linear_bound_by_arg
            bound = sine_linear_bound_by_arg.instantiate(
                    {theta: self.angle.operand})
        elif InSet(self.angle, RealPos).readily_provable():
            # for theta > 0, use the line y = theta
            from . import sine_linear_bound_by_arg_pos
            bound = sine_linear_bound_by_arg_pos.instantiate(
                    {theta: self.angle})
        elif InSet(self.angle, RealNonNeg).readily_provable():
            # for theta >= 0, use the line y = theta
            from . import sine_linear_bound_by_arg_nonneg
            bound = sine_linear_bound_by_arg_nonneg.instantiate(
                    {theta: self.angle})
        elif InSet(self.angle, RealNonPos).readily_provable():
            # for theta <= 0 try the chord y = (2/pi)(theta)
            # but will only work for -Pi/2 <= theta <= 0
            from . import sine_linear_bound_nonpos
            bound = sine_linear_bound_nonpos.instantiate(
                    {theta: self.angle})
        else: # not clear what this then does
            from . import sine_linear_bound
            _theta = Abs(self.angle)
            bound = sine_linear_bound.instantiate(
                    {theta: _theta})
        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        from proveit.numbers import Complex
        from . import real_closure
        if Real.readily_includes(number_set):
            # While we are at it, let's prove that this Sin
            # is within an appropriate interval (e.g. between +/-1).
            self.deduce_in_interval()
            if InSet(self, number_set).proven():
                return InSet(self, number_set).prove()
        if number_set in (Real, Complex):
            closure = real_closure.instantiate({theta:self.angle})
            if number_set == Real:
                return closure
            return InSet(self, number_set).prove()
        self.deduce_in_interval()
        if InSet(self, number_set).readily_provable():
            return InSet(self, number_set).conclude_as_last_resort()
        raise NotImplementedError(
                "'Sin.deduce_in_number_set()' not implemented for the "
                "%s set" % str(number_set))        

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        return self.deduce_in_interval()
