# from proveit import USE_DEFAULTS, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership
# from proveit.numbers import num
# from proveit import m, A, x


class KElemSubsetsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set of
    k-element subsets of a set.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)


class KElemSubsetsNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set of
    k-element subsets of a set.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)
