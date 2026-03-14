from proveit import Operation, Literal, prover
from proveit import K, V, W
from proveit.logic import SetMembership

class LinMaps(Operation):
    '''
    A linear map expression represents the set of linear mappings
    from one specified vector space to another.
    '''
    
    _operator_ = Literal(string_format=r'LinMaps', 
                         latex_format= r'\textrm{LinMaps}',
                         theory=__file__)

    def __init__(self, from_vspace, to_vspace, *, styles=None):
        '''
        Denote the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Operation.__init__(self, LinMaps._operator_, 
                           (from_vspace, to_vspace),
                           styles=styles)
        self.from_vspace = from_vspace
        self.to_vspace = to_vspace

    def membership_object(self, element):
        return LinMapsMembership(element, self)

    def _formatted(self, format_type, **kwargs):
        formatted_from_vspace = self.from_vspace.formatted(format_type,
                                                           fence=True)
        formatted_to_vspace = self.to_vspace.formatted(format_type,
                                                       fence=True)
        if format_type=='latex':
            return (r'\mathcal{L}\left[' + formatted_from_vspace
                    + r' \rightarrow ' + formatted_to_vspace + r'\right]')
        return (r'L[' + formatted_from_vspace
                + r' -> ' + formatted_to_vspace + r']')

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


class LinMapsMembership(SetMembership):
    '''
    Defines methods that apply to InSet(element, LinMap(X, Y))
    objects via InClass.__getattr__ which calls 
    LinMap.membership_object(element)
    to return a LinMapMembership object.    
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)
