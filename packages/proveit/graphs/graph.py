from proveit import Function, Literal
from proveit import E, V
from proveit.logic import ClassMembership

class Graphs(Literal):
    '''
    Graphs represents the (mathematical) class of graphs, to which
    any specific graph G = (V, E) of vertices and edges belongs.
    This class might not be necessary, but is modeled on the
    HilbertSpacesLiteral class in the linear_algebra/inner_products
    theory package.
    '''

    # the literal string for representing the class of Graphs
    def __init__(self, *, styles=None):
        Literal.__init__(self, string_format='Graphs', 
                         latex_format=r'\textrm{Graphs}',
                         styles=styles)

    def membership_object(self, element):
        return GraphsMembership(element, self)

    @property
    def is_proper_class(self):
        '''
        Graphs consitute a proper class (i.e. instead of a set).
        This indicates that InClass() should be used instead of
        InSet() when this is a domain.
        '''
        return True


class GraphsMembership(ClassMembership):

    def __init__(self, element, domain):
        from . import Graphs
        ClassMembership.__init__(self, element, domain)
        if domain != Graphs():
            raise TypeError("domain expected to be Graphs, not %s"
                            %domain.__class__)

    # def conclude(): see if and when needed

class Graph(Function):
    '''
    Graph(V, E) represents a graph with vertex set V and edge set E.
    The vertex set V is conceptualized as a set of vertices such as
    {x_1, ..., x_n} but might appear or be interpreted as a set of
    geometric points such as {(x1, y1), (x2, y2), ..., (xn, yn)}.
    The edge set E is conceptualized as a set of pairs of vertices,
    such as {x1 x2, x2 x3, ..., xn x1}, which might eventually take
    the form of a set of 2-element sets or a set of ordered pairs.
    '''

    # the literal operator of the Graph operation
    _operator_ = Literal(string_format='G',
                         latex_format=r'\textrm{G}',
                         theory=__file__)

    def __init__(self, V, E, *, styles=None):
        '''
        Create a graph G(V,E) with vertex set V and edge set E.
        '''
        self.vertex_set = V
        self.edge_set   = E
        Function.__init__(
                self, Graph._operator_, (V, E), styles=styles)

class Vertices(Function):
    '''
    Given a graph G(V, E) with vertex set V and edge set E,
    Vertices(G(V, E)) represents the set V of vertices ---
    that is, Vertices(G(V,E)) = V.
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

class Edges(Function):
    '''
    Given a graph G(V, E) with vertex set V and edge set E,
    Edges(G(V, E)) represents the set E of vertices ---
    that is, Edges(G(V,E)) = E.
    '''

    # the literal operator of the Vertices operation
    _operator_ = Literal(string_format='E',
                         latex_format=r'\mathrm{E}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Given a graph G(V,E) = (V,E), represent the edge set of G.
        '''
        self.graph = G
        Function.__init__(
                self, Edges._operator_, G, styles=styles)


class Path(Graph):
    '''
    Path(V,E) represents a path. A Path is a non-empty graph
    P = (V,E) with vertex set V and edge set E such that:

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
        Create or represent a Path, Path(V,E), with vertex set V
        and edge set E.
        '''
        self.vertex_set = V
        self.edge_set   = E
        Function.__init__(
                self, Path._operator_, (V, E), styles=styles)


class EndPoints(Function):
    '''
    EndPoints(P) denotes the set of two endpoints of a Path P = (V, E),
    where Path P has vertex set V and edge set E. EndPoints(P) will be
    a subset of the Path P's vertex set V.
    EndPoints(P) will not "know" the original path P whence it came.
    '''

    # the literal operator of the EndPoints operator
    _operator_ = Literal(
            string_format='EndPts', latex_format=r'\text{EndPts}',
            theory=__file__)

    def __init__(self, P, *, styles=None):
        '''
        Create the endpoints set EndPts(P) for Path P.
        '''
        Function.__init__(
                self, EndPoints._operator_, P, styles=styles)
