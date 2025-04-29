from proveit.logic import SetMembership, SetNonmembership


class EndpointsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set Endpoints(P)
    of the endpoints of path P.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)


class EndpointsNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set 
    Endpoints(P) of the endpoints of path P.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)