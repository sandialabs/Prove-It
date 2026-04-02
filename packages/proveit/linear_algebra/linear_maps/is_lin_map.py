from proveit import Operation, Function, Literal, prover, ClassMembership
from proveit import K, V, W
from proveit.logic import SetMembership

class IsLinMap(ClassMembership):
    '''
    IsLinMap denotes membership in the class of linear mappings
    from one specified vector space to another.  Unlike the set of
    linear mappings (see lin_map.py), the domain of functions in this
    class is not resctricted to only the 'from' vector space.  That is,
    functions with broader domains are in the class but not the set of
    linear maps.
    '''
    
    _operator_ = Literal(string_format=r'IsLinMap', 
                         latex_format=r'\textrm{IsLinMap}',
                         theory=__file__)

    def __init__(self, func, from_vspace, to_vspace, *, styles=None):
        '''
        Denote the set of linear maps that map from and to the given
        vectors spaces.
        '''
        ClassMembership.__init__(self, IsLinMap._operator_, 
                                 func, from_vspace, to_vspace, styles=styles)
        self.from_vspace = from_vspace
        self.to_vspace = to_vspace
    
    def formatted_class(self, format_type):
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
