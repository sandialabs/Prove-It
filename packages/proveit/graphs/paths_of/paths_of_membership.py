from proveit.logic import SetMembership, SetNonmembership


class PathsOfMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set PathsOf(G)
    of all paths in graph G.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)


class PathsOfNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set PathsOf(G)
    of all paths in graph G.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)