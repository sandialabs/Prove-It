from proveit import Function, Literal

class Paths(Function):
    '''
    Given a graph G = G(V, E) with vertex set V and edge set E,
    Paths(G) represents the set of all paths in the graph G.
    A Path (in an undirected graph G) is a non-empty graph P = (V,E)
    with vertex set V and edge set E such that:

        V = {x0, x1, ..., xk},
        E = {{x0,x1}, {x1,x2}, ..., {x_{k-1},x_{k}},

    where the x_{i} are all distinct. The vertices x0 and xk are said
    to be linked by the path P and are called its endvertices, or
    endpoints, or simply its ends. The vertices x1, ..., x_{k-1} are
    the inner vertices of P. The number of edges in the path P,
    denoted ||P||, is its length (in this example, ||P|| = k).
    '''

    # the literal operator of the Paths operation
    _operator_ = Literal(string_format='Paths',
                         latex_format=r'\mathrm{Paths}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the set of paths in the graph G = G(V,E) with vertex
        set V and edge set E.
        '''
        Function.__init__(
                self, Paths._operator_, G, styles=styles)