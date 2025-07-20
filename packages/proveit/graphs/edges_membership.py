from proveit import e, E, V, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership
from proveit.graphs import Graph


class EdgesMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    Edges(G(V,E)) of the edges E of graph G.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Edges(Graph(V,E))], deduce and return:
            [elem in Edges(Graph(V,E))] = [elem in E]
        '''
        from . import edges_membership_def
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return edges_membership_def.instantiate(
                {e:element, V:_V_sub, E:_E_sub },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in Edges(Graph(V,E))], return: [elem in E]
        (i.e. an expression, not a Judgment)
        '''
        if isinstance(self.domain.operand, Graph):
            from proveit.logic import InSet
            element = self.element
            _E = self.domain.graph.edge_set
            return InSet(element, _E)
        else:
            raise NotImplementedError(
                "EdgesMembership.as_defined() was called on "
                f"self = {self.expr} with domain = {self.expr.domain}, "
                "but the method is implemented only for domains of the "
                "form Edges(G) where G is an explicit Graph object "
                "of the form G = Graph(V,E) with a named edge set E.")

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in Edges(Graph(V,E))],
        derive and return [elem in E], knowing or assuming self.
        '''
        from . import edges_membership_unfolding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return edges_membership_unfolding.instantiate(
            {e:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem in Edges(Graph(V,E))], and
        knowing or assuming [elem in E] (and that E is a subset
        of [V]^2, a subset of the set of 2-element subsets of V)
        derive and return self.
        '''
        from . import edges_membership_folding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return edges_membership_folding.instantiate(
            {e:element, V:_V_sub, E:_E_sub}, auto_simplify=False)


class EdgesNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set
    Edges(G(V,E)) of the edges E of graph G.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for EdgesNonmembership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem not in Edges(Graph(V,E))], deduce and
        return: [elem not in Edges(Graph(V,E))] = [elem not in E].
        '''

        from . import edges_nonmembership_def
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return edges_nonmembership_def.instantiate(
                {e:element, V:_V_sub, E:_E_sub },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem not in Edges(Graph(V,E))],
        return: [elem not in E] (i.e. an expression, not a Judgment)
        '''
        if isinstance(self.domain.operand, Graph):
            from proveit.logic import NotInSet
            element = self.element
            _E = self.domain.graph.edge_set
            return NotInSet(element, _E)
        else:
            raise NotImplementedError(
                "EdgesNonmembership.as_defined() was called on "
                f"self = {self.expr} with domain = {self.expr.domain}, "
                "but the method is implemented only for domains of the "
                "form Edges(G) where G is an explicit Graph object "
                "of the form G = Graph(V,E) with a named edge set E.")

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem not in Edges(Graph(V,E))],
        derive and return [elem not in E], knowing or assuming self,
        (and that E is a subset of [V]^2, i.e., a subset of the set
        of 2-element subsets of V).
        '''
        from . import edges_nonmembership_unfolding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return edges_nonmembership_unfolding.instantiate(
            {e:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem not in Edges(Graph(V,E))], and
        knowing or assuming [elem not in E] (and that E is a subset
        of [V]^2, a subset of the set of 2-element subsets of V)
        derive and return self.
        '''
        from . import edges_nonmembership_folding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return edges_nonmembership_folding.instantiate(
            {e:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

