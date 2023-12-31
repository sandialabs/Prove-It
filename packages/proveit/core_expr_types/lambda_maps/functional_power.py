from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class FunctionalPower(Operation):
    '''
    Represents repeated compositions of a function with itself.
    '''
    
    # operator of the (functional) Power operation
    _operator_ = Literal(string_format='FnPow', latex_format=r'{\rm FnPow}', 
                         theory=__file__)
    
    def __init__(self, function, power, *, styles=None):
        Operation.__init__(self, FunctionalPower._operator_, (function, power),
                           styles=styles)
        self.function = function
        self.power = power

    def string(self, **kwargs):
        format_type = 'string'
        func_str = self.function.formatted(
            format_type, fence=True, force_fence=True)
        pow_str = self.power.formatted(format_type, fence=False)
        return func_str + "^<%s>"%pow_str

    def latex(self, **kwargs):
        format_type = 'latex'
        func_str = self.function.formatted(
            format_type, fence=True, force_fence=True)
        pow_str = self.power.formatted(format_type, fence=False)
        return func_str + r"^{\langle %s \rangle}"%pow_str
