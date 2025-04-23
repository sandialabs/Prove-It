from proveit import Literal, Function
from proveit import n, x


class KPowerSet(Function):
    '''
    Given a S and a natural number k <= |S|, KPowerSet(S, k)
    represents the set of all k-element subsets of S, denoted [S]^{k}.
    Such sets are similar in principle to the PowerSet of S (which
    contains [S]^{k}) and arise often enough in set theory and 
    combinatorics to have somewhat standard notation.
    In Prove-It, [S]^{k} arises in the context of graph theory,
    using k = 2 to describe the superset of possible graph edges in
    a simple graph.
    '''

    # operator for the KPowerSet function.
    _operator_ = Literal(string_format='KPowerSet', theory=__file__)

    def __init__(self, src_set, k, *, styles=None):
        '''
        Create the representation of the set of all k-element subsets
        of the set src_set.
        '''
        Function.__init__(self, KPowerSet._operator_, (src_set, k),
                          styles=styles)

    def string(self, **kwargs):
        return (
            '[' + self.operands[0].string() + ']^'
                + self.operands[1].string())

    def latex(self, **kwargs):
        return (
            r'\left[' + self.operands[0].latex()
                      + r'\right]^{' + self.operands[1].latex() + r'}')

    # TO BE UPDATED ONCE MEMBERSHIP DEFINED
    
    # def membership_object(self, element):
    #     from .k_elem_subsets_membership import KElemSubsetsMembership
    #     return KElemSubsetsMembership(element, self)

    # def nonmembership_object(self, element):
    #     from .k_elem_subsets_membership import KElemSubsetsNonmembership
    #     return KElemSubsetsNonmembership(element, self)
