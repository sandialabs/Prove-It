from proveit import Function, Literal
from proveit.logic import ClassMembership
from proveit.graphs import Graph

class Paths(Literal):
    '''
    Paths() represents the set of all graphs that are (undirected)
    paths. A undirected path is a non-empty graph P = (V,E)
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

    # the literal string for representing the class of Paths
    def __init__(self, *, styles=None):
        Literal.__init__(self, string_format='Paths', 
                         latex_format=r'\textrm{Paths}',
                         styles=styles)

    @property
    def is_proper_class(self):
        '''
        Paths consitute a proper class (i.e. instead of a set).
        This indicates that InClass() should be used instead of
        InSet() when this is a domain.
        '''
        return True

    def membership_object(self, element):
        from .paths_membership import PathsMembership
        return PathsMembership(element, self)

    def nonmembership_object(self, element):
        from .paths_membership import PathsNonmembership
        return PathsNonmembership(element, self)


class Path(Graph):
    '''
    Path(V,E) represents the special type of graph called a path,
    with vertex set V and edge set E. A path is a non-empty graph
    P = (V,E) with vertex set V and (possibly empty) edge set E such
    that:

        V = {x0, x1, ..., xk}, E = {x0x1, x1x2, ..., x_{k-1}x_{k}},

    where the x_{i} are all distinct. The vertices x0 and xk are said
    to be linked by the path P and are called its endvertices, or
    endpoints, or simply its ends. The vertices x1, ..., x_{k-1} are
    the inner vertices of P. The number of edges in the path P,
    denoted ||P||, is its length (in this example, ||P|| = k).
    '''

    # the literal operator of the Path operator
    _operator_ = Literal(string_format='Path',
                         latex_format=r'\text{Path}',
                         theory=__file__)

    def __init__(self, V, E, *, styles=None):
        '''
        Create or represent a path, Path(V,E), with vertex set V
        and edge set E. If explicit sets of vertices and edges are
        provided, they are NOT currently verified to represent a
        valid path.
        '''
        self.vertex_set = V
        self.edge_set   = E
        Function.__init__(self, Path._operator_, (V, E), styles=styles)

