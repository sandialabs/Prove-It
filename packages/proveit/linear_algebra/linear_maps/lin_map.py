from proveit import Operation, Function, Literal

class LinMap(Function):
    '''
    A linear map expression represents the set of linear mappings
    from on vector space to another vector space.
    '''
    
    _operator_ = Literal(string_format=r'LINMAP', 
                         latex_format=r'\mathcal{L}',
                         theory=__file__)
    
    def __init__(self, from_vspace, to_vspace, *, styles=None):
        '''
        Create the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Function.__init__(self, LinMap._operator_, 
                          (from_vspace, to_vspace),
                          styles=styles)

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
        Create the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Function.__init__(self, LinMapAdd._operator_, operands,
                          styles=styles)
