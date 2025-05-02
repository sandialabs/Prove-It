from proveit import Function, Literal

'''
Consider:
(1) Changing the current Paths(G) function to PathsOf(G)
(2) Adding a new Paths class to denote the set of all graphs
    that are also paths. Paths() would then be a subset (subclass?)
    of Graphs().
(3) Move the Path(V,E) class from graph.py to here to represent
    a specific path with vertex set V and edge set E.
    A path P = Path(V, E) would be an element of the Paths() class,
    and also an element of the Graphs() class.
This might work well.
'''

class PathsOf(Function):
    '''
    Given a graph G = G(V, E) with vertex set V and edge set E,
    PathsOf(G) represents the set of all paths in the graph G.
    A Path (in an undirected graph G) is a non-empty graph P = (V,E)
    with non-empty vertex set V and (possibly empty) edge set E such
    that:
            V = {x0, x1, ..., xk},
            E = {{x0,x1}, {x1,x2}, ..., {x_{k-1},x_{k}},

    where the x_{i} are all distinct. The vertices x0 and xk are said
    to be linked by the path P and are called its endvertices, or
    endpoints, or simply its ends. The vertices x1, ..., x_{k-1} are
    the inner vertices of P. The number of edges in the path P,
    denoted ||P||, is its length (in this example, ||P|| = k).
    '''

    # the literal operator of the PathsOf operation
    _operator_ = Literal(string_format='PathsOf',
                         latex_format=r'\mathrm{PathsOf}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the set of paths in the graph G = G(V,E) with vertex
        set V and edge set E.
        '''
        Function.__init__(
                self, PathsOf._operator_, G, styles=styles)

    # the membership stuff still to be updated!
    def membership_object(self, element):
        from .paths_of_membership import PathsOfMembership
        return PathsOfMembership(element, self)

    def nonmembership_object(self, element):
        from .paths_of_membership import PathsOfNonmembership
        return PathsOfNonmembership(element, self)
