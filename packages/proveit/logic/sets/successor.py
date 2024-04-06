from proveit import Function, Literal

class OrdinalSuccessor(Function):
    '''
    Represents the successor function for the the von Neumann ordinals.
    '''

    _operator_ = Literal(string_format='S', latex_format='S', theory=__file__)
    
    def __init__(self, w, *, styles=None):
        r'''
        Successor of a set w: w union {w}.
        '''
        Function.__init__(self, OrdinalSuccessor._operator_, w, styles=styles)
