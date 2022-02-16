from proveit import Function, Literal, USE_DEFAULTS, prover, relation_prover, equality_prover
from proveit import theta
from proveit.logic import InSet
from proveit.numbers import Real, RealPos, RealNeg, RealNonNeg, RealNonPos
from proveit.numbers import Abs, deduce_number_set

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
        deduce_number_set(_theta)
        if (Less(zero, _theta).proven() and
                Less(_theta, pi).proven()):
            return sine_pos_interval.instantiate({theta:_theta})
        elif (LessEq(zero, _theta).proven() and
                LessEq(_theta, pi).proven()):
            return sine_nonneg_interval.instantiate(
                    {theta:_theta})
        elif (Less(Neg(pi), _theta).proven() and
                Less(_theta, zero).proven()):
            return sine_neg_interval.instantiate(
                    {theta:_theta})
        elif (Less(Neg(pi), _theta).proven() and
                Less(_theta, zero).proven()):
            return sine_neg_interval.instantiate(
                    {theta:_theta})
        elif (LessEq(Neg(pi), _theta).proven() and
                LessEq(_theta, zero).proven()):
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
        '''
        from . import (sine_linear_bound, sine_linear_bound_pos,
                       sine_linear_bound_nonneg, sine_linear_bound_neg,
                       sine_linear_bound_nonpos)

        deduce_number_set(self.angle)

        if isinstance(self.angle, Abs):
            bound = sine_linear_bound.instantiate(
                    {theta: self.angle.operand})
        elif InSet(self.angle, RealPos).proven():
            bound = sine_linear_bound_pos.instantiate(
                    {theta: self.angle})
        elif InSet(self.angle, RealNeg).proven():
            bound = sine_linear_bound_neg.instantiate(
                    {theta: self.angle})
        elif InSet(self.angle, RealNonNeg).proven():
            bound = sine_linear_bound_nonneg.instantiate(
                    {theta: self.angle})
        elif InSet(self.angle, RealNonPos).proven():
            bound = sine_linear_bound_nonpos.instantiate(
                    {theta: self.angle})
        else:
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
        if number_set in (Real, Complex):
            closure = real_closure.instantiate({theta:self.angle})
            if number_set == Real:
                return closure
            return InSet(self, number_set).prove()
        if number_set in (RealPos, RealNeg, RealNonNeg, RealNonPos):
            # Maybe use deduce_interval to help
            interval = self.deduce_in_interval().domain
            raise NotImplementedError(
                    "Implementation not quite finished")        
        
        raise NotImplementedError(
                "'Sin.deduce_in_number_set()' not implemented for the "
                "%s set" % str(number_set))        

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        return self.deduce_in_interval()

