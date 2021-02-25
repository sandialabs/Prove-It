from proveit import Function, Literal, USE_DEFAULTS
from proveit import theta
from proveit.logic import InSet
from proveit.numbers import Real, RealPos, RealNeg, RealNonNeg, RealNonPos

class Sin(Function):
    # operator of the Abs operation.
    _operator_ = Literal(string_format='sin', theory=__file__)
    
    def __init__(self, angle):
        Function.__init__(self, Sin._operator_, angle)
        self.angle = angle
    
    def latex(self, **kwargs):
        return r'\sin{' + self.operand.latex(fence=True) + r'}'
    
    def deduce_linear_bound(self, assumptions=USE_DEFAULTS):
        from . import (sine_linear_bound, sine_linear_bound_pos,
                       sine_linear_bound_nonneg, sine_linear_bound_neg,
                       sine_linear_bound_nonpos)
        if InSet(self.angle, RealPos).proven(assumptions):
            return sine_linear_bound_pos.instantiate(
                    {theta:self.angle}, assumptions=assumptions)
        elif InSet(self.angle, RealNeg).proven(assumptions):
            return sine_linear_bound_neg.instantiate(
                    {theta:self.angle}, assumptions=assumptions)
        elif InSet(self.angle, RealNonNeg).proven(assumptions):
            return sine_linear_bound_nonneg.instantiate(
                    {theta:self.angle}, assumptions=assumptions)
        elif InSet(self.angle, RealNonPos).proven(assumptions):
            return sine_linear_bound_nonpos.instantiate(
                    {theta:self.angle}, assumptions=assumptions)
        else:
            return sine_linear_bound.instantiate(
                    {theta:self.angle}, assumptions=assumptions)
            