from proveit import Operation, Literal

class InvImage(Operation):
    '''
    Represents a function (operator) that may be applied to a set or 
    tuple (ordered set) for applying the inverse of a function to each
    element.
    '''
    _operator_ = Literal('INV_IMAGE', theory=__file__)
    
    def __init__(self, elem_function, *, styles=None):
        Operation.__init__(self, InvImage._operator_, elem_function, 
                       styles=styles)
        self.elem_function = elem_function
    
    def string(self, **kwargs):
        return self.elem_function.string(fence=True) + '^*'
    
    def latex(self, fence=False, **kwargs):
        return self.elem_function.latex(fence=True) + '^{\leftarrow}'
    
            
