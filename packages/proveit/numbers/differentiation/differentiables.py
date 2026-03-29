from proveit import Operation, Literal

class Differentiables(Operation):
    '''
 Differentiables(U) would be the set of functions that are differentiable over the set U  ⊂ ℝ.
    '''
    _operator_ = Literal('Differentiables', r'\textrm{Differentiables}',
                         theory=__file__)
    
    def __init__(self, U, *, styles=None):
        Operation.__init__(self, Differentiables._operator_, U, 
                       styles=styles)
        self.U = U
       
    # def membership_object(self, element):
    #     from .functions_membership import FunctionsMembership
    #     return FunctionsMembership(element, self)
    
    def latex(self, **kwargs):
        U_str = self.U.latex(fence=True)
       
        return (r'{\rm Differentiables}(' + U_str + r' )')

    def string(self, **kwargs):
         U_str = self.U.latex(fence=True)
         return (r'Differentiables(' + U_str + r' )')