from proveit import USE_DEFAULTS, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership
from proveit.numbers import num
from proveit import m, n, x, G
from proveit.graphs import GraphMembership, GraphNonmembership


class GraphUnionMembership(GraphMembership):
    '''
    GraphUnionMembership represents membership in a union of
    multiple graphs and provides methods that apply to membership
    in a union of graphs. See GraphUnion class for related concepts.
    Note that the membership relation is InGraph instead of InSet.
    '''

    def __init__(self, element, domain):
        GraphMembership.__init__(self, element, domain)

    # for future consideration, borrowed from sets UnionMembership
    # def side_effects(self, judgment):
    #     '''
    #     Unfold the enumerated set membership as a side-effect.
    #     '''
    #     yield self.unfold

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Given self = elem in (G1 U G2 U ... U Gn), deduce and return 
            [elem in (G1 U G2 U ... U Gn)] = 
            [(elem in G1) V (elem in G2) V ... V (elem in Gn)].
        '''
        from . import graph_union_membership_def
        element = self.element
        operands = self.domain.operands
        _G_sub = operands
        _n_sub = _G_sub.num_elements()
        return graph_union_membership_def.instantiate(
                {n: _n_sub, x: element, G: _G_sub}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem in (G1 U G2 U ... U Gn)], return
        [(elem in G1) V (elem in G2) V ... V (elem in Gn)].
        '''
        from proveit.logic import Or
        from proveit.graphs import InGraph
        element = self.element
        return Or(*self.domain.operands.map_elements(
                lambda subset : InGraph(element, subset)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in (G1 U G2 U ... U Gn)], derive and return
        [(elem in G1) V (elem in G2) V ... V (elem in Gn)].
        '''
        from . import membership_unfolding 
        element = self.element
        operands = self.domain.operands
        _G_sub = operands
        _n_sub = _G_sub.num_elements()
        return membership_unfolding.instantiate(
            {n:_n_sub, x:element, G:_G_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem in (G1 U G2 U ... U Gn)], and knowing or
        assuming [[elem in G1] V [elem in G2] V ... V [elem in Gn]],
        derive and return self.
        '''
        from . import membership_folding
        element = self.element
        operands = self.domain.operands
        _G_sub = operands
        _n_sub = _G_sub.num_elements()
        return membership_folding.instantiate(
                {n:_n_sub, x: element, G:_G_sub})

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce that self = (elem in (G1 U G2 U ... U Gn)) is in Bool.
        Used as helper function elsewhere and not usually explicitly
        called by the user.
        '''
        from . import union_membership_is_bool
        element = self.element
        operands = self.domain.operands
        _G_sub = operands
        _n_sub = _G_sub.num_elements()
        return union_membership_is_bool.instantiate(
                {n:_n_sub, x:element, G:_G_sub})


class GraphUnionNonmembership(GraphNonmembership):
    '''
    Defines methods that apply to non-membership in a union of graphs.
    '''

    def __init__(self, element, domain):
        GraphNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for union nonmembership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self=[elem not in (G1 U G2 U ... U Gn)], deduce and return:
        |- [elem not in (G1 U G2 U ... U Gn)]
         = [(elem not in G1) AND (elem not in G2) AND ...
                AND elem not in Gn].
        '''

        from . import nonmembership_equiv
        element = self.element
        operands = self.domain.operands
        _G_sub = operands
        _n_sub = _G_sub.num_elements()
        return nonmembership_equiv.instantiate(
            {n: _n_sub, x: element, G: _G_sub}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem not in (G1 U G2 U ... U Gn)], return
        [(elem not in G1) AND (elem not in G2) AND ... 
         AND (elem not in Gn)].
        '''
        from proveit.logic import And, NotInSet
        from proveit.graphs import NotInGraph
        element = self.element
        return And(*self.domain.operands.map_elements(
                lambda subset : NotInGraph(element, subset)))

    @prover
    def conclude(self, **defaults_config):
        '''
        From self = [elem not in (G1 U G2 U ... U Gn)], and knowing
        or assuming [elem not in G1] AND [elem not in G2] AND ...
        AND [elem not in Gn], derive and return self.
        '''
        from . import nonmembership_folding
        element = self.element
        operands = self.domain.operands
        _G_sub = operands
        _n_sub = _G_sub.num_elements()
        return nonmembership_folding.instantiate(
            {n:_n_sub, x:element, G:_G_sub})

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce that self = (elem NotIn (G1 U G2 U ... U Gn)) is in Bool.
        Used as helper function elsewhere and not usually explicitly
        called by the user.
        '''
        from . import union_nonmembership_is_bool
        element = self.element
        operands = self.domain.operands
        _G_sub = operands
        _n_sub = _G_sub.num_elements()
        return union_nonmembership_is_bool.instantiate(
                {n:_n_sub, x:element, G:_G_sub})

