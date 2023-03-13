from proveit import Function, Literal

class OrthoNormBases(Function):
    '''
    A OrthoNormBases expression denotes the set of vector sets that
    form an orthonormal basis within a given vector space.
    '''
    
    _operator_ = Literal(
            string_format=r'O.N.Bases', latex_format=r'\textrm{O.N.Bases}',
            theory=__file__)

    
    def __init__(self, vec_space, *, styles=None):
        Function.__init__(self, OrthoNormBases._operator_, 
                          vec_space, styles=styles)
        self.vec_space = vec_space
