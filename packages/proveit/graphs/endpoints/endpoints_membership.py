from proveit.logic import SetMembership, SetNonmembership


class EndpointsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set Endpoints(P)
    of the endpoints of path P.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Endpoints(P)], where P is a non-trivial
        path (i.e. a path with at least one edge), deduce and return:
            [elem in Vertices(Graph(V,E))] = [elem in V]
        '''

        from . import membership_def
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return membership_def.instantiate(
                {v:element, V:_V_sub, E:_E_sub },auto_simplify=False)


class EndpointsNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set 
    Endpoints(P) of the endpoints of path P.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)