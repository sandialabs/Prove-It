from proveit import Function, Literal

class Edges(Function):
    '''
    Given a graph G(V, E) with vertex set V and edge set E,
    Edges(G(V, E)) represents the set E of vertices ---
    that is, Edges(G(V,E)) = E. The notation will use E(G),
    in which case we might see things like E(G) = E, but the operator
    E will appear in mathrm to distinguish it from the set E in
    italics.
    '''

    # the literal operator of the Vertices operation
    _operator_ = Literal(string_format='Edges',
                         latex_format=r'\mathrm{Edges}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Given a graph G(V,E) = (V,E), represent the edge set of G.
        '''
        self.graph = G
        Function.__init__(
                self, Edges._operator_, G, styles=styles)

    def membership_object(self, element):
        from .edges_membership import EdgesMembership
        return EdgesMembership(element, self)

    def nonmembership_object(self, element):
        from .edges_membership import EdgesNonmembership
        return EdgesNonmembership(element, self)