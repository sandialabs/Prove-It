from proveit import Operation, Literal

class LinMapAdd(Operation):
    '''
    Express the addition of linear maps which is defined via
    (S + T)(v) = S(v) + T(v)
    where S, T in LinMap(V, W) and v in V.
    
    We use the same symbol as number addition, but we treat it as
    it's own operation with it's own definition.
    '''

    _operator_ = Literal(string_format='+', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        '''
        Denote the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Operation.__init__(self, LinMapAdd._operator_, operands,
                           styles=styles)
