from proveit import Function, Literal

class Bases(Function):
    '''
    A Bases expression denotes the set of vector sets that are both a
    spanning set and linearly independent within a given vector space.
    '''
    
    _operator_ = Literal(
            string_format=r'Bases', latex_format=r'\textrm{Bases}',
            theory=__file__)

    
    def __init__(self, vec_space, *, styles=None):
        Function.__init__(self, Bases._operator_, 
                          vec_space, styles=styles)
        self.vec_space = vec_space

# OrthoNormBases is defined in the inner_products package.
        