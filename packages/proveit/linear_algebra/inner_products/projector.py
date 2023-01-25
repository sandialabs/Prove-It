from proveit import Function, Literal

class Proj(Function):
    '''
    A projector is a linear map from a Hilbert space to itself
    that projects onto a subspace.  Elements fully within the
    subspace map to themselves.  Elements outside of the subspace
    map to the zero vector.
    '''

    _operator_ = Literal(string_format='Proj', latex_format=r'\textrm{Proj}',
                         theory=__file__)

    def __init__(self, hilbert_space, subspace, *, styles=None):
        '''
        Denote a projector on
        '''
        Function.__init__(self, Proj._operator_, 
                          (hilbert_space, subspace),
                          styles=styles)
