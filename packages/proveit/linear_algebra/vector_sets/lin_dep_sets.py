from proveit import Function, Literal

class LinDepSets(Function):
    '''
    A LinDepSets expression denotes the set of vectors sets that are
    linearly dependent (not linearly independent) within a given vector
    space.
    '''
    
    _operator_ = Literal(
            string_format=r'LinDepSets', latex_format=r'\textrm{LinDepSets}',
            theory=__file__)

    
    def __init__(self, vec_space, *, styles=None):
        Function.__init__(self, LinDepSets._operator_, 
                          vec_space, styles=styles)
        self.vec_space = vec_space
