from proveit import Function, Literal

class VecZero(Function):
    '''
    The VecZero Function equate the the zero vector of a given
    vector space.  The zero vector satisfies the property that
        v + 0 = v
    for any v in the vector space.
    '''
    
    _operator_ = Literal(string_format=r'0', latex_format=r'\vec{0}',
                         theory=__file__)
    
    def __init__(self, vec_space, *, styles=None):
        Function.__init__(self, VecZero._operator_, vec_space, 
                          styles=styles)
