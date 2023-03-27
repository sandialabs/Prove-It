from proveit import Function, Literal

class Span(Function):
    '''
    The span of a set of vectors is the vectors space formed
    from linear combinations of those vectors.
    '''
    
    _operator_ = Literal(
            string_format=r'Span', latex_format=r'\textrm{Span}',
            theory=__file__)

    
    def __init__(self, *vecs, styles=None):
        Function.__init__(self, Span._operator_, 
                          vecs, styles=styles)
        self.vecs = vecs

    
class SpanningSets(Function):
    '''
    A SpanningSets expression denotes the set of spanning sets
    for a given vector space.
    '''
    
    _operator_ = Literal(
            string_format=r'SpanningSets', latex_format=r'\textrm{SpanningSets}',
            theory=__file__)

    
    def __init__(self, vec_space, *, styles=None):
        Function.__init__(self, SpanningSets._operator_, 
                          vec_space, styles=styles)
        self.vec_space = vec_space
