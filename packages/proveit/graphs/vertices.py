from proveit import u, v, G, equality_prover, Function, Literal

class Vertices(Function):
    '''
    Given a graph G(V, E) with vertex set V and edge set E,
    Vertices(G(V, E)) represents the set V of vertices ---
    that is, Vertices(G(V,E)) = V.
    '''

    # the literal operator of the Vertices operation
    _operator_ = Literal(string_format='Vertices',
                         latex_format=r'\mathrm{Vertices}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Given a graph G(V,E) = (V,E), represent the vertex set of G.
        '''
        self.graph = G
        Function.__init__(
                self, Vertices._operator_, G, styles=styles)

    def membership_object(self, element):
        from .vertices_membership import VerticesMembership
        return VerticesMembership(element, self)

    def nonmembership_object(self, element):
        from .vertices_membership import VerticesNonmembership
        return VerticesNonmembership(element, self)


class Degree(Function):
    '''
    Degree(v, G), denoted deg(v), represents the degree or valency of
    the vertex v occuring in the graph G. For an undirected graph with
    no loops, deg(v) will be equal to the number of edges incident
    with vertex v. For vertex v in a directed graph, deg(v) will equal
    the sum of the in-degree and out-degree of vertex v.
    '''

    # the literal operator of the Degree operation
    _operator_ = Literal(string_format='deg',
                         latex_format=r'\mathrm{deg}',
                         theory=__file__)

    def __init__(self, v, G, *, styles=None):
        '''
        Given a vertex v of a graph G(V,E) = (V,E), represent the
        degree of the vertex v.
        '''
        Function.__init__(
                self, Degree._operator_, (v, G), styles=styles)


class AdjacentVertices(Function):
    '''
    For vertices u, v in graph G, AdjacentVertices(u, v, G) denotes
    the claim that vertices u and v are adjacent in graph G (i.e., 
    AdjacentVertices(u, v, G) means that {u, v} is an edge in graph G).
    We use the full 'AdjacentVertices()' for naming and calling the
    class to distinguish the situation from adjacent edges.
    '''
    # the literal operator of the Adjacent operation
    _operator_ = Literal(string_format='Adjacent',
                         latex_format=r'\mathrm{Adjacent}',
                         theory=__file__)

    def __init__(self, u, v, G, *, styles=None):
        '''
        Given vertices u, v in graph G, represent the claim that
        vertices u and v are adjacent in G.
        '''
        self.graph = G
        self.vertices = (u, v)
        Function.__init__(
                self, AdjacentVertices._operator_, (u, v, G), styles=styles)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = AdjacentVertices(u, v, G), deduce and return the
        equality: AdjacentVertices(u, v, G) = {u, v} in Edges(G).
        '''
        from . import adjacent_vertices_def
        _u_sub = self.operands[0]
        _v_sub = self.operands[1]
        _G_sub = self.operands[2]
        return adjacent_vertices_def.instantiate(
            {u:_u_sub, v:_v_sub, G:_G_sub}, auto_simplify=False)

