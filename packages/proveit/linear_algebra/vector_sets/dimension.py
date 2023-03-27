from proveit import Function, Literal

class Dim(Function):
    '''
    A Dimension expression denotes the dimension of a vectors space
    which is the number of vectors in a basis.
    '''
    
    _operator_ = Literal(
            string_format=r'Dim', latex_format=r'\textrm{Dim}',
            theory=__file__)

    
    def __init__(self, vec_space, *, styles=None):
        Function.__init__(self, Dim._operator_, 
                          vec_space, styles=styles)
        self.vec_space = vec_space
