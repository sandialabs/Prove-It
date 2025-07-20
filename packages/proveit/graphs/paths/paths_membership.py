# from proveit.logic import SetMembership, SetNonmembership
from proveit.logic import ClassMembership, ClassNonmembership



class PathsMembership(ClassMembership):
    '''
    Defines methods that apply to membership in the set Paths(G)
    of all paths in a graph G.
    '''

    def __init__(self, element, domain):
        ClassMembership.__init__(self, element, domain)


class PathsNonmembership(ClassNonmembership):
    '''
    Defines methods that apply to non-membership in the set Paths(G)
    of all paths in a graph G.
    '''

    def __init__(self, element, domain):
        ClassNonmembership.__init__(self, element, domain)