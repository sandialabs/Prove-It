from proveit import equality_prover, Function, Literal
from proveit import E, G, V
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


class Order(Function):
    '''
    Order(G), denoted |G|, represents the order of graph G, giving
    the number of vertices in graph G. This will be equivalent to
    |Vertices(G)|.
    '''
    # literal operator of the Order operation.
    _operator_ = Literal(string_format='Order', theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent Order(G), the order of graph G, equivalent
        to the number of vertices in G.
        '''
        self.graph = G
        Function.__init__(
                self, Order._operator_, G, styles=styles)

    def string(self, **kwargs):
        return '|' + self.operand.string() + '|'

    def latex(self, **kwargs):
        return r'\left|' + self.operand.latex() + r'\right|'

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = |G|, deduce and return the equality:
        |G| = |Vertices(G)|.
        '''
        from . import graph_order_def
        _G_sub = self.operand
        return graph_order_def.instantiate({G:_G_sub}, auto_simplify=False)


class Size(Function):
    '''
    Size(G), denoted ||G||, represents the size of graph G, meaning
    the number of edges in graph G. This will be equivalent to
    |Edges(G)|.
    '''
    # literal operator of the Size operation.
    _operator_ = Literal(string_format='Size', theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent Size(G), the size of graph G, equivalent
        to the number of edges in G.
        '''
        self.graph = G
        Function.__init__(
                self, Size._operator_, G, styles=styles)

    def string(self, **kwargs):
        return '||' + self.operand.string() + '||'

    def latex(self, **kwargs):
        return r'\left\|' + self.operand.latex() + r'\right\|'

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = ||G||, deduce and return the equality:
        ||G|| = |Edges(G)|.
        '''
        from . import graph_size_def
        _G_sub = self.operand
        return graph_size_def.instantiate({G:_G_sub}, auto_simplify=False)


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
    
    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = Connected(G), deduce and return the equality:
        Connected(G) = A, where A represents the statement that,
        for all vertices u, v in G, there exists a u-v path in G.
        '''
        from . import connected_def
        _G_sub = self.operand
        return connected_def.instantiate({G:_G_sub}, auto_simplify=False)


class HasEulerianTrail(Function):
    '''
    HasEulerTrail(G) is a propositional function (or predicate)
    claiming that graph G has an Eulerian trail (i.e., G has a
    walk that uses each and every edge of G exactly once).
    '''

    # the literal operator of the HasEulerTrail operation
    _operator_ = Literal(string_format='HasEulerianTrail',
                         latex_format=r'\textrm{HasEulerianTrail}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the propositional function HasEulerianTrail(G),
        claiming graph G has an Eulerian trail.
        '''
        self.graph = G
        Function.__init__(
                self, HasEulerianTrail._operator_, G, styles=styles)


class HasEulerianCircuit(Function):
    '''
    HasEulerCircuit(G) is a propositional function (or predicate)
    claiming that graph G has an Eulerian circuit (i.e., G has a
    closed walk that uses each and every edge of G exactly once).
    '''

    # the literal operator of the HasEulerCircuit operation
    _operator_ = Literal(string_format='HasEulerianCircuit',
                         latex_format=r'\textrm{HasEulerianCircuit}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the propositional function HasEulerianCircuit(G),
        claiming graph G has an Eulerian circuit.
        '''
        self.graph = G
        Function.__init__(
                self, HasEulerianCircuit._operator_, G, styles=styles)

