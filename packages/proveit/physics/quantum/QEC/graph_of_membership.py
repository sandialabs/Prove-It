from proveit import v, G, prover
from proveit.logic import SetMembership

'''
This module is dedicated to classes and methods related to 
memberships in sets or classes arising in the graph_of module.
The code is modeled on recent previous work in the graphs module,
such as the vertices and vertices_membership code, which was itself
modeled on the more general examples found in the logic/sets modules.
'''

class InteriorVerticesMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    InteriorVertices(G) of interior vertices of the graph G, where
    the graph G is a graph representation of a surface code, such as
    MergedBoundsGraphOfSurfaceCode(S), or a graph representation of
    an error chain E with respect to the graph of a surface code S,
    such as MergedBoundsGraphOfZError(E, S). These are quite
    specialized memberships, but it is still useful in various
    contexts to have some standard membership methods developed.
    Much of this development is delayed while we work out a good
    definition for the interior vs. boundary vertices in the 
    GraphOf() and MergedBoundsGraphOf() graphs.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    # placeholder for future dev, borrowed from graphs/vertices
    # @equality_prover('defined', 'define')
    # def definition(self, **defaults_config):
    #     '''
    #     From self = [elem in Vertices(Graph(V,E))], deduce and return:
    #         [elem in Vertices(Graph(V,E))] = [elem in V]
    #     '''

    #     from . import vertices_membership_def
    #     element = self.element
    #     _V_sub  = self.domain.graph.vertex_set
    #     _E_sub  = self.domain.graph.edge_set
    #     return vertices_membership_def.instantiate(
    #             {v:element, V:_V_sub, E:_E_sub },auto_simplify=False)

    # placeholder for future dev, borrowed from graphs/vertices
    # def as_defined(self):
    #     '''
    #     From self = [elem in Vertices(Graph(V,E))], return: [elem in V]
    #     (i.e. an expression, not a Judgment). Only works if the
    #     Vertices domain has as an operand an actual Graph object
    #     Graph(V,E) with a specified vertex set V.
    #     '''
    #     if isinstance(self.domain.operand, Graph):
    #         from proveit.logic import InSet
    #         element = self.element
    #         _V =  self.domain.graph.vertex_set
    #         return InSet(element, _V)
    #     else:
    #         raise NotImplementedError(
    #             "VerticesMembership.as_defined() was called on "
    #             f"self = {self.expr} with domain = {self.expr.domain}, "
    #             "but the method is implemented only for domains of the "
    #             "form Vertices(G) where G is an explicit Graph object "
    #             "of the form G = Graph(V,E) with a named vertex set V.")

    # placeholder for future dev, borrowed from graphs/vertices
    # @prover
    # def unfold(self, **defaults_config):
    #     '''
    #     From self = [elem in Vertices(Graph(V,E))],
    #     derive and return [elem in V], knowing or assuming self.
    #     '''
    #     from . import vertices_membership_unfolding
    #     element = self.element
    #     _V_sub  = self.domain.graph.vertex_set
    #     _E_sub  = self.domain.graph.edge_set
    #     return vertices_membership_unfolding.instantiate(
    #         {v:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

    # placeholder for future dev, borrowed from graphs/vertices
    # @prover
    # def conclude(self, **defaults_config):
    #     '''
    #     Called on self = [elem in Vertices(Graph(V,E))], and
    #     knowing or assuming [elem in V] (and that E is a subset
    #     of [V]^2, a subset of the set of 2-element subsets of V)
    #     derive and return self.
    #     '''
    #     from . import vertices_membership_folding
    #     element = self.element
    #     _V_sub  = self.domain.graph.vertex_set
    #     _E_sub  = self.domain.graph.edge_set
    #     return vertices_membership_folding.instantiate(
    #         {v:element, V:_V_sub, E:_E_sub}, auto_simplify=False)

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce that self = (elem in InteriorVertices(G)) is in Bool.
        Used as helper function elsewhere and not usually explicitly
        called by the user.
        '''
        from . import interior_vertices_membership_is_bool
        _G_sub = self.domain.operand
        _v_sub = self.element
        return interior_vertices_membership_is_bool.instantiate(
                {G:_G_sub, v:_v_sub})
