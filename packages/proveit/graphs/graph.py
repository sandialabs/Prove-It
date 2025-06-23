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
    _operator_ = Literal(string_format='Graph',
                         latex_format=r'\textrm{Graph}',
                         theory=__file__)

    def __init__(self, V, E, *, styles=None):
        '''
        Create a graph G(V,E) with vertex set V and edge set E.
        '''
        self.vertex_set = V
        self.edge_set   = E
        Function.__init__(
                self, Graph._operator_, (V, E), styles=styles)


class Connected(Function):
    '''
    Connected(G) is a propositional function (or predicate)
    representing the claim that graph G is connected (i.e., that
    for every pair (u, v) of vertices in G, there exists a u-v path
    in G).
    '''

    # the literal operator of the Connected operation
    _operator_ = Literal(string_format='Connected',
                         latex_format=r'\textrm{Connected}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the propositional function Connected(G),
        claiming graph G is connected.
        '''
        self.graph = G
        Function.__init__(
                self, Connected._operator_, G, styles=styles)



