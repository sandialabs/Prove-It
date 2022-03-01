from proveit import Operation, Function, Literal

class Image(Operation):
    '''
    Represents a function (operator) that may be applied to a set or 
    tuple (ordered set) for applying a function to each element.
    '''
    _operator_ = Literal('IMAGE', theory=__file__)
    
    def __init__(self, elem_function, *, styles=None):
        Operation.__init__(self, Image._operator_, elem_function, 
                       styles=styles)
        self.elem_function = elem_function
    
    def string(self, **kwargs):
        return self.elem_function.string(fence=True) + '^*'
    
    def latex(self, fence=False, **kwargs):
        return self.elem_function.latex(fence=True) + r'^{\rightarrow}'

def image_of_set(f, A):
    return Function(Image(f), A)