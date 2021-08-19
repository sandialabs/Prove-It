from proveit import Operation, Literal

class ScalarMult(Operation):
    '''
    The ScalarMult operation is the default for the scalar 
    multiplication of a vector and may also be used for scalar
    multiplication of a matrix (in the same manner since matrix
    spaces are vector spaces).
    '''
    # the literal operator of the MatrixProd operation
    # perhaps use SCALAR_PROD for string?
    # latex_format try using \; in place of a blank space
    _operator_ = Literal(string_format=r'*', latex_format=r'\thinspace',
                         theory=__file__)

    def __init__(self, scalar, scaled, *, styles=None):
        r'''
        Product between a scalar and a matrix (or vector).
        '''
        Operation.__init__(self, ScalarMult._operator_, [scalar, scaled],
                           styles=styles)
        self.scalar = scalar
        self.scaled = scaled
