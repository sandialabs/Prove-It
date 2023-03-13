from proveit import Function, Literal

class OrthoProj(Function):
    '''
    A orthogonal projector is a linear map from a Hilbert space to 
    itself that projects onto a subspace.  Elements fully within the
    subspace map to themselves.  Elements outside of the subspace
    map to the zero vector.
    '''

    _operator_ = Literal(string_format='OrthoProj', 
                         latex_format=r'\textrm{OrthoProj}',
                         theory=__file__)

    def __init__(self, hilbert_space, subspace, *, styles=None):
        '''
        Denote an orthogonal projector that projects from a
        space to a subspace.
        '''
        Function.__init__(self, OrthoProj._operator_, 
                          (hilbert_space, subspace),
                          styles=styles)
