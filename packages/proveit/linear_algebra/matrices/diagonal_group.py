from proveit import Function, Literal

class Diagonal(Function):
    '''
    Diagonal groups are the diagonal matrices.
    '''

    # the literal operator of the SU operation
    _operator_ = Literal(string_format='D', latex_format=r'\textrm{D}',
                         theory=__file__)

    def __init__(self, _n, *, styles=None):
        '''
        Create some D(n), the diagonal matrics of degree n.
        '''
        Function.__init__(self, Diagonal._operator_, _n, styles=styles)
        self.degree = _n
