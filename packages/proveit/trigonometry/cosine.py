from proveit import Function, Literal

class Cos(Function):
    # operator of the Cos operation.
    _operator_ = Literal(string_format='cos', theory=__file__)
    
    def __init__(self, angle, *, styles=None):
        Function.__init__(self, Cos._operator_, angle, styles=styles)
        self.angle = angle
    
    def latex(self, **kwargs):
        return r'\cos{' + self.operand.latex(fence=True) + r'}'
