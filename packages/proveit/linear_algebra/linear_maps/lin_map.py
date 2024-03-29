from proveit import Operation, Function, Literal, prover
from proveit import K, V, W
from proveit.logic import SetMembership

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
        Denote the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Function.__init__(self, LinMap._operator_, 
                          (from_vspace, to_vspace),
                          styles=styles)
        self.from_vspace = from_vspace
        self.to_vspace = to_vspace

    def membership_object(self, element):
        return LinMapMembership(element, self)

    @prover
    def deduce_as_vec_space(self, **defaults_config):
        '''
        Prove that this linear map is a vector space.
        '''
        from proveit.linear_algebra import deduce_as_vec_space
        from . import lin_map_is_vec_space
        _K = deduce_as_vec_space(self.from_vspace).domain.field
        _V, _W = self.from_vspace, self.to_vspace
        return lin_map_is_vec_space.instantiate({K:_K, V:_V, W:_W})


class LinMapMembership(SetMembership):
    '''
    Defines methods that apply to InSet(element, LinMap(X, Y))
    objects via InClass.__getattr__ which calls 
    LinMap.membership_object(element)
    to return a LinMapMembership object.    
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

        
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
        Function.__init__(self, LinMapAdd._operator_, operands,
                          styles=styles)
