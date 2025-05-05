from proveit import v, E, V, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership
from proveit.graphs import Graph


class VerticesMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    Vertices(G(V,E)) of the vertices V of graph G.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Vertices(Graph(V,E))], deduce and return:
            [elem in Vertices(Graph(V,E))] = [elem in V]
        '''

        from . import membership_def
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return membership_def.instantiate(
                {v:element, V:_V_sub, E:_E_sub },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in Vertices(Graph(V,E))], return: [elem in V]
        (i.e. an expression, not a Judgment). Only works if the
        Vertices domain has as an operand an actual Graph object
        Graph(V,E) with a specified vertex set V.
        '''
        if isinstance(self.domain.operand, Graph):
            from proveit.logic import InSet
            element = self.element
            _V =  self.domain.graph.vertex_set
            return InSet(element, _V)
        else:
            raise NotImplementedError(
                "VerticesMembership.as_defined() called on "
                f"self = {self.expr} with domain = {self.expr.domain}, "
                "but the method is implemented only for domains of "
                "the form Vertices(G) where G is an explicit Graph "
                "object of the form Graph(V,E) with a named vertex set.")

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in Vertices(Graph(V,E))],
        derive and return [elem in V], knowing or assuming self.
        '''
        from . import membership_unfolding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return membership_unfolding.instantiate(
            {v:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem in Vertices(Graph(V,E))], and
        knowing or assuming [elem in V] (and that E is a subset
        of [V]^2, a subset of the set of 2-element subsets of V)
        derive and return self.
        '''
        from . import membership_folding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return membership_folding.instantiate(
            {v:element, V:_V_sub, E:_E_sub}, auto_simplify=False)



class VerticesNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set
    Vertices(G(V,E)) of the vertices V of graph G.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for VerticesNonmembership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem not in Vertices(Graph(V,E))], deduce and
        return: [elem not in Vertices(Graph(V,E))] = [elem not in V].
        '''

        from . import nonmembership_def
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return nonmembership_def.instantiate(
                {v:element, V:_V_sub, E:_E_sub },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem not in Vertices(Graph(V,E))],
        return: [elem not in V] (i.e. an expression, not a Judgment)
        '''
        if isinstance(self.domain.operand, Graph):
            from proveit.logic import NotInSet
            element = self.element
            _V =  self.domain.graph.vertex_set
            return NotInSet(element, _V)
        else:
            raise NotImplementedError(
                "VerticesNonmembership.as_defined() called on "
                f"self = {self.expr} with domain = {self.expr.domain}, "
                "but the method is implemented only for domains of "
                "the form Vertices(G) where G is an explicit Graph "
                "object of the form Graph(V,E) with a named vertex set.")

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem not in Vertices(Graph(V,E))],
        derive and return [elem not in V], knowing or assuming self,
        (and that E is a subset of [V]^2, i.e., a subset of the set
        of 2-element subsets of V).
        '''
        from . import nonmembership_unfolding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return nonmembership_unfolding.instantiate(
            {v:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem not in Vertices(Graph(V,E))], and
        knowing or assuming [elem not in V] (and that E is a subset
        of [V]^2, a subset of the set of 2-element subsets of V)
        derive and return self.
        '''
        from . import nonmembership_folding
        element = self.element
        _V_sub  = self.domain.graph.vertex_set
        _E_sub  = self.domain.graph.edge_set
        return nonmembership_folding.instantiate(
            {v:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

