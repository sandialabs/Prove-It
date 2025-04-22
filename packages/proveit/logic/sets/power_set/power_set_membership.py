from proveit.logic import SetMembership, SetNonmembership


class PowerSetMembership(SetMembership):
    '''
    Defines methods that apply to membership in the power set P(S) of
    a set S.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)


class PowerSetNonembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set of
    k-element subsets of a set.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)
