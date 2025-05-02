from proveit import Function, Literal

class Vertices(Function):
    '''
    Given a graph G(V, E) with vertex set V and edge set E,
    Vertices(G(V, E)) represents the set V of vertices ---
    that is, Vertices(G(V,E)) = V. The notation will use V(G),
    in which case we might see things like V(G) = V, but the operator
    V will appear in mathrm to distinguish it from the set V in
    italics.
    '''

    # the literal operator of the Vertices operation
    _operator_ = Literal(string_format='V',
                         latex_format=r'\mathrm{V}',
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

