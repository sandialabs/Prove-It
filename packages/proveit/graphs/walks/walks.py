from proveit import Function, Literal
from proveit.logic import ClassMembership
from proveit.graphs import Graph

class Walks(Function):
    '''
    Walks(G) represents the set of walks in the simple undirected
    graph G. A walk W in a simple undirected graph G is a sequence
    (u = v0, v1, ..., v = vk) of vertices of G such that consecutive
    vertices in the sequence are adjacent in G --- in other words,
    every pair {v_{i}, v_{i+1}} of vertices (for i in {0, 1, ..., k-1})
    corresponds to an edge in G. u and v are called the endvertices
    or endpoints of the walk, and a walk from u to v is often referred
    to as a u-v walk. The vertices v1, v2, ..., v_{k-1} are called
    internal vertices. The number of edges in the walk W, denoted
    by ||W||, is the length of the walk (in this example, ||W|| = k).
    The number of vertices in the Walk sequence W, including
    multiplicities of repeated vertices, is denoted |W|, analogous
    to the notation for the order of a graph, |G|.
    '''

    # the literal operator of the Walks operation
    _operator_ = Literal(string_format='Walks',
                         latex_format=r'\textrm{Walks}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the set Walks(G) of all walks in graph G.
        '''
        self.graph = G
        Function.__init__(
                self, Walks._operator_, G, styles=styles)

class Walk(Function):
    '''
    Walk(S, G) represents a walk in the simple undirected graph G
    with vertex sequence S. See the description above under Walks(G)
    for a definition of a walk in graph G.
    '''

    # the literal operator of the Walk(S,G) operation
    _operator_ = Literal(string_format='Walk',
                         latex_format=r'\textrm{Walk}',
                         theory=__file__)

    def __init__(self, S, G, *, styles=None):
        '''
        Represent Walk(S, G), the walk in G consisting of vertex
        sequence S in the simple undirected graph G.
        '''
        self.graph = G
        self.vertex_sequence = S
        Function.__init__(
                self, Walk._operator_, (S, G), styles=styles)

class WalkLength(Function):
    '''
    WalkLength(W), denoted ||W||, represents the length of walk W
    (where W could be a walk or one of the special cases of a
    trail, path, circuit, etc., all of which area also walks)
    equivalent to the number of edges crossed during the walk
    (including multiplicities). For example, given a walk
    W = Walk(S, G) in graph G with vertex sequence
        S = (a, b, c, b, d, e),
    we have WalkLength(W) = ||W|| = 5. Notice that ||W|| is always
    equal to len(S) - 1, where len(S) is the length of sequence S.
    '''

    # literal operator of the WalkLength operation.
    _operator_ = Literal(string_format='Len', theory=__file__)

    def __init__(self, W, *, styles=None):
        '''
        Represent WalkLength(W), the length of walk W, equivalent
        to the number of edges traveled during walk W.
        '''
        self.walk = W
        Function.__init__(
                self, WalkLength._operator_, W, styles=styles)

    def string(self, **kwargs):
        return '||' + self.operand.string() + '||'

    def latex(self, **kwargs):
        return r'\left\|' + self.operand.latex() + r'\right\|'


class Trail(Function):
    '''
    Trail(S, G) represents a trail in the simple undirected graph G
    with vertex sequence S. A trail is a walk (see the description
    above in the Walks(G) class) in which no edge is repeated.
    '''

    # the literal operator of the Trail(S,G) operation
    _operator_ = Literal(string_format='Trail',
                         latex_format=r'\textrm{Trail}',
                         theory=__file__)

    def __init__(self, S, G, *, styles=None):
        '''
        Represent Trail(S, G), the trail in G consisting of vertex
        sequence S in the simple undirected graph G.
        '''
        self.graph = G
        self.vertex_sequence = S
        Function.__init__(
                self, Trail._operator_, (S, G), styles=styles)


class Path(Function):
    '''
    Path(S, G) represents a path in the simple undirected graph G
    with vertex sequence S. A path is a walk (see the description
    above in the Walks(G) class) in which no vertex (and thus no edge)
    is repeated.
    '''

    # the literal operator of the Path(S,G) operation
    _operator_ = Literal(string_format='Path',
                         latex_format=r'\textrm{Path}',
                         theory=__file__)

    def __init__(self, S, G, *, styles=None):
        '''
        Represent Path(S, G), the path in G consisting of vertex
        sequence S in the simple undirected graph G.
        '''
        self.graph = G
        self.vertex_sequence = S
        Function.__init__(
                self, Path._operator_, (S, G), styles=styles)


class EndVertices(Function):
    '''
    EndVertices(W) represent the set of endvertices or endpoints of
    the walk W (and recall that trails, paths, circuits, and cycles
    are special cases of walks). For example, given a walk
    W = Walk(S, G) in graph G with vertex sequence
        S = (a, b, c, b, d, e),
    we have EndVertices(W) = {a, e}. Notice that EndVertices(W) will
    have a single element when W is a circuit or a cycle.
    '''

    # the literal operator of the EndVertices(W) operation
    _operator_ = Literal(string_format='EndVertices',
                         latex_format=r'\textrm{EndVertices}',
                         theory=__file__)

    def __init__(self, W, *, styles=None):
        '''
        Represent EndVertices(W), the set of endvertices of walk W.
        '''
        self.walk = W
        Function.__init__(
                self, EndVertices._operator_, W, styles=styles)


class HasEulerTrail(Function):
    '''
    HasEulerTrail(G) is a propositional function (or predicate)
    claiming that graph G has an Eulerian trail (i.e., G has a
    walk that uses each and every edge of G exactly once).
    '''

    # the literal operator of the HasEulerTrail operation
    _operator_ = Literal(string_format='HasEulerTrail',
                         latex_format=r'\textrm{HasEulerTrail}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the propositional function HasEulerTrail(G),
        claiming graph G has an Eulerian trail.
        '''
        self.graph = G
        Function.__init__(
                self, HasEulerTrail._operator_, G, styles=styles)


class HasEulerCircuit(Function):
    '''
    HasEulerCircuit(G) is a propositional function (or predicate)
    claiming that graph G has an Eulerian circuit (i.e., G has a
    closed walk that uses each and every edge of G exactly once).
    '''

    # the literal operator of the HasEulerCircuit operation
    _operator_ = Literal(string_format='HasEulerCircuit',
                         latex_format=r'\textrm{HasEulerCircuit}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent the propositional function HasEulerCircuit(G),
        claiming graph G has an Eulerian circuit.
        '''
        self.graph = G
        Function.__init__(
                self, HasEulerCircuit._operator_, G, styles=styles)


# class Paths(Literal):
#     '''
#     Paths() represents the set of all graphs that are (undirected)
#     paths. A undirected path is a non-empty graph P = (V,E)
#     with non-empty vertex set V and (possibly empty) edge set E such
#     that:
#             V = {x0, x1, ..., xk},
#             E = {{x0,x1}, {x1,x2}, ..., {x_{k-1},x_{k}},

#     where the x_{i} are all distinct. The vertices x0 and xk are said
#     to be linked by the path P and are called its endvertices, or
#     endpoints, or simply its ends. The vertices x1, ..., x_{k-1} are
#     the inner vertices of P. The number of edges in the path P,
#     denoted ||P||, is its length (in this example, ||P|| = k).
#     '''

#     # the literal string for representing the class of Paths
#     def __init__(self, *, styles=None):
#         Literal.__init__(self, string_format='Paths', 
#                          latex_format=r'\textrm{Paths}',
#                          styles=styles)

#     @property
#     def is_proper_class(self):
#         '''
#         Paths consitute a proper class (i.e. instead of a set).
#         This indicates that InClass() should be used instead of
#         InSet() when this is a domain.
#         '''
#         return True

#     def membership_object(self, element):
#         from .paths_membership import PathsMembership
#         return PathsMembership(element, self)

#     def nonmembership_object(self, element):
#         from .paths_membership import PathsNonmembership
#         return PathsNonmembership(element, self)


# class Path(Graph):
#     '''
#     Path(V,E) represents the special type of graph called a path,
#     with vertex set V and edge set E. A path is a non-empty graph
#     P = (V,E) with vertex set V and (possibly empty) edge set E such
#     that:

#         V = {x0, x1, ..., xk}, E = {x0x1, x1x2, ..., x_{k-1}x_{k}},

#     where the x_{i} are all distinct. The vertices x0 and xk are said
#     to be linked by the path P and are called its endvertices, or
#     endpoints, or simply its ends. The vertices x1, ..., x_{k-1} are
#     the inner vertices of P. The number of edges in the path P,
#     denoted ||P||, is its length (in this example, ||P|| = k).
#     '''

#     # the literal operator of the Path operator
#     _operator_ = Literal(string_format='Path',
#                          latex_format=r'\text{Path}',
#                          theory=__file__)

#     def __init__(self, V, E, *, styles=None):
#         '''
#         Create or represent a path, Path(V,E), with vertex set V
#         and edge set E. If explicit sets of vertices and edges are
#         provided, they are NOT currently verified to represent a
#         valid path.
#         '''
#         self.vertex_set = V
#         self.edge_set   = E
#         Function.__init__(self, Path._operator_, (V, E), styles=styles)



