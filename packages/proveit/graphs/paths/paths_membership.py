from proveit.logic import SetMembership, SetNonmembership


class PathsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set Paths(G)
    of all paths in a graph G.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)


class PathsNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set Paths(G)
    of all paths in a graph G.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)