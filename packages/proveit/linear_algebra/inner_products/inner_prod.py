from proveit import Operation, Literal

class InnerProd(Operation):
    _operator_ = Literal(
            string_format=r'InnerProd', latex_format=r'\textrm{InnerProd}',
            theory=__file__)
    
    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, InnerProd._operator_,
                           (a, b), styles=styles)
    
    def string(self, **kwargs):
        a, b = self.operands
        return '<' + a.string() + ', ' + b.string() + '>'
    
    def latex(self, **kwargs):
        a, b = self.operands
        return (r'\left \langle ' + a.latex() + ', ' 
                + b.latex() + r'\right \rangle')
