from proveit import equality_prover, Function, Literal
from proveit.logic import ClassMembership
from proveit.graphs import Graph,  Size

class Walks(Function):
    '''
    Walks(k, G) represents the set of walks of length k in the simple
    undirected graph G. A walk W in a simple undirected graph G is a
    sequence (u = v0, v1, ..., v = vk) of vertices of G such that
    consecutive vertices in the sequence are adjacent in G ---
    in other words, every pair {v_{i}, v_{i+1}} of vertices
    (for i in {0, 1, ..., k-1}) corresponds to an edge in G.
    u and v are called the endvertices or endpoints of the walk, and
    a walk from u to v is often referred to as a u-v walk.
    The vertices v1, v2, ..., v_{k-1} are called internal vertices.
    The number of edges in the walk W, denoted by ||W||, is the
    length of the walk (in this example, ||W|| = k).
    The number of vertices in the walk W, including multiplicities
    of repeated vertices, is denoted |W|, analogous to the notation
    for the order of a graph, |G|.
    Ultimately, the vertex sequence characterizing a walk W is
    conceptualized as a function, S: {0, 1, ..., k} -> Vertices(G),
    and thus a walk is itself conceptualized as a special kind of
    function.
    Trails, paths, circuits, and cycles are all special cases of walks.
    '''

    # the literal operator of the Walks operation
    _operator_ = Literal(string_format='Walks',
                         latex_format=r'\textrm{Walks}',
                         theory=__file__)

    def __init__(self, k, G, *, styles=None):
        '''
        Represent Walks(k, G), the set of all walks of
        length k in graph G.
        '''
        self.graph = G
        self.length = k
        Function.__init__(
                self, Walks._operator_, (k, G), styles=styles)

    def membership_object(self, element):
        from .walks_membership import WalksMembership
        return WalksMembership(element, self)

#     def nonmembership_object(self, element):
#         from .walks_membership import WalksNonmembership
#         return WalksNonmembership(element, self)


class ClosedWalks(Function):
    '''
    ClosedWalks(k, G) represents the set of closed walks of length k
    in the simple undirected graph G. See the description in the Walks
    class for details about walks more generally. A closed walk is a
    walk in which the first and last vertex are the same. Closed walks
    are important in part because ClosedWalks(k, G) is a superset for
    Circuits(k, G) and Cycles(k, G).
    '''

    # the literal operator of the ClosedWalks operation
    _operator_ = Literal(string_format='ClosedWalks',
                         latex_format=r'\textrm{ClosedWalks}',
                         theory=__file__)

    def __init__(self, k, G, *, styles=None):
        '''
        Represent ClosedWalks(k, G), the set of all closed walks of
        length k in graph G.
        '''
        self.graph = G
        self.length = k
        Function.__init__(
                self, ClosedWalks._operator_, (k, G), styles=styles)

    def membership_object(self, element):
        from .walks_membership import ClosedWalksMembership
        return ClosedWalksMembership(element, self)

#     def nonmembership_object(self, element):
#         from .walks_membership import WalksNonmembership
#         return WalksNonmembership(element, self)


class Trails(Function):
    '''
    Trails(k, G) represents the set of trails of length k in the
    simple graph G. A trail is a walk in which no edge is repeated.
    See the Walks() class above for a definition of walk.
    A trail with endvertices u and v is often called a u-v trail.
    '''

    # the literal operator of the Trails operation
    _operator_ = Literal(string_format='Trails',
                         latex_format=r'\textrm{Trails}',
                         theory=__file__)

    def __init__(self, k, G, *, styles=None):
        '''
        Represent Trails(k, G), the set of all trails of
        length k in graph G.
        '''
        self.graph = G
        self.length = k
        Function.__init__(
                self, Trails._operator_, (k, G), styles=styles)

    def membership_object(self, element):
        from .walks_membership import TrailsMembership
        return TrailsMembership(element, self)

    # def nonmembership_object(self, element):
    #     from .walks_membership import TrailsNonmembership
    #     return TrailsNonmembership(element, self)


class ClosedTrails(Function):
    '''
    ClosedTrails(k, G) represents the set of closed trails of length
    k in the simple graph G. A trail is a walk in which no edge is
    repeated; a _closed_ trail is a trail that begins and ends at the
    same vertex, and can be conceptualized as a special case of a
    closed walk.
    '''

    # the literal operator of the ClosedTrails operation
    _operator_ = Literal(string_format='ClosedTrails',
                         latex_format=r'\textrm{ClosedTrails}',
                         theory=__file__)

    def __init__(self, k, G, *, styles=None):
        '''
        Represent ClosedTrails(k, G), the set of all closed trails of
        length k in graph G.
        '''
        self.graph = G
        self.length = k
        Function.__init__(
                self, ClosedTrails._operator_, (k, G), styles=styles)

    def membership_object(self, element):
        from .walks_membership import ClosedTrailsMembership
        return ClosedTrailsMembership(element, self)

    # def nonmembership_object(self, element):
    #     from .walks_membership import TrailsNonmembership
    #     return TrailsNonmembership(element, self)


class Paths(Function):
    '''
    Paths(k, G) represents the set of paths of length k in the simple
    graph G. A path is a walk in which no vertex (and thus no edge)
    is repeated. See the Walks() class above for a definition of walk.
    A path with endvertices u and v is often called a u-v path.
    '''

    # the literal operator of the Paths operation
    _operator_ = Literal(string_format='Paths',
                         latex_format=r'\textrm{Paths}',
                         theory=__file__)

    def __init__(self, k, G, *, styles=None):
        '''
        Represent Paths(k, G), the set of all paths of
        length k in graph G.
        '''
        self.graph = G
        self.length = k
        Function.__init__(
                self, Paths._operator_, (k, G), styles=styles)

    def membership_object(self, element):
        from .walks_membership import PathsMembership
        return PathsMembership(element, self)

#     def nonmembership_object(self, element):
#         from .walks_membership import PathsNonmembership
#         return PathsNonmembership(element, self)


class Circuits(Function):
    '''
    Circuits(k, G) represents the set of circuits of length k >= 3 in
    the simple undirected graph G. A circuit in a graph G is a closed
    trail of length 3 or more in G. Because a circuit is a closed
    trail, a circuit begins and ends at the same vertex without
    repeating any edges, and a circuit can be described by choosing
    any of its vertices as the beginning (and ending) vertex. See the
    description above in the Walks class for more details about walks.
    '''

    # the literal operator of the Circuits operation
    _operator_ = Literal(string_format='Circuits',
                         latex_format=r'\textrm{Circuits}',
                         theory=__file__)

    def __init__(self, k, G, *, styles=None):
        '''
        Represent Circuits(k, G), the set of all circuits of
        length k in graph G.
        '''
        self.graph = G
        self.length = k
        Function.__init__(
                self, Circuits._operator_, (k, G), styles=styles)

    def membership_object(self, element):
        from .walks_membership import CircuitsMembership
        return CircuitsMembership(element, self)

#     def nonmembership_object(self, element):
#         from .walks_membership import CircuitsNonmembership
#         return CircuitsNonmembership(element, self)


class EulerianCircuits(Function):
    '''
    EulerianCircuits(G) represents the set of Eulerian circuits
    of the simple undirected graph G. An Eulerian circuit in G is
    a circuit in G that uses every edge of G. Since it uses every
    edge, there is no length parameter k that appears in other
    types of walks. Because it is a circuit, we expect an Eulerian
    circuit to be non-trivial: it should consist of at least 3 edges.
    The set of EulerianCircuits(G) could be an empty set.
    '''

    # the literal operator of the EulerianCircuits operation
    _operator_ = Literal(string_format='EulerianCircuits',
                         latex_format=r'\textrm{EulerianCircuits}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent EulerianCircuits(G), the set of all Eulerian
        circuits in graph G.
        '''
        self.graph = G
        self.length = Size(G)
        Function.__init__(
                self, EulerianCircuits._operator_, G, styles=styles)

    def membership_object(self, element):
        from .walks_membership import EulerianCircuitsMembership
        return EulerianCircuitsMembership(element, self)

#     def nonmembership_object(self, element):
#         from .walks_membership import CircuitsNonmembership
#         return CircuitsNonmembership(element, self)


class Cycles(Function):
    '''
    Cycles(k, G) represents the set of cycles of length k in
    the simple undirected graph G. A cycle in a graph G can be
    thought of as a "closed path": a cycle is a circuit without 
    repeating any vertices (except for the beginning and ending
    vertices). A cycle of length k is often referred to as a k-cycle.
    A 3-cycle is often simply referred to as a triangle. A cycle of
    odd length is called an odd cycle; a cycle of even length is
    called an even cycle. See the description above in the Walks
    class for more details about walks.
    '''

    # the literal operator of the Cycles operation
    _operator_ = Literal(string_format='Cycles',
                         latex_format=r'\textrm{Cycles}',
                         theory=__file__)

    def __init__(self, k, G, *, styles=None):
        '''
        Represent Cycles(k, G), the set of all cycles of
        length k (also called k-cycles) in graph G.
        '''
        self.graph = G
        self.length = k
        Function.__init__(
                self, Cycles._operator_, (k, G), styles=styles)

    def membership_object(self, element):
        from .walks_membership import CyclesMembership
        return CyclessMembership(element, self)

#     def nonmembership_object(self, element):
#         from .walks_membership import CyclesNonmembership
#         return CyclesNonmembership(element, self)


class WalkLength(Function):
    '''
    WalkLength(W), denoted ||W||, represents the length of walk W
    (where W could be a walk or one of the special cases of a
    trail, path, circuit, etc., all of which area also walks),
    equivalent to the number of edges crossed during the walk
    (including multiplicities). For example, given a walk
    W in Walks(5, G) in graph G with vertex sequence
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


class ClosedWalk(Function):
    '''
    ClosedWalk(W) is a propositional function (or predicate)
    claiming that walk W is closed (i.e., that the endvertices of
    walk W are equal). Recall that trails, paths, circuits, and
    cycles are all special cases of walks.
    '''

    # the literal operator of the ClosedWalk() operation
    _operator_ = Literal(string_format='Closed',
                         latex_format=r'\textrm{Closed}',
                         theory=__file__)

    def __init__(self, W, *, styles=None):
        '''
        Represent the propositional function ClosedWalk(G),
        claiming walk W is closed.
        '''
        self.walk = W
        Function.__init__(
                self, ClosedWalk._operator_, W, styles=styles)

class EdgeSequence(Function):
    '''
    Given a walk W in Walks(k, G) consisting of vertex sequence S in
    graph G, EdgeSeq(W) represents the sequence of edges traveled
    along the walk, which for a simple graph is completely
    determined by the vertex sequence S. The number of edges in
    EdgeSequence(W) is the length of the walk W, represented with
    WalkLength(W).
    '''

    # the literal operator of the EdgeSequence operation
    _operator_ = Literal(string_format='EdgeSeq',
                         latex_format=r'\mathrm{EdgeSeq}',
                         theory=__file__)

    def __init__(self, W, *, styles=None):
        '''
        Given a walk W = Walk(S, G) in graph G, represent the
        sequence of edges traveled during the walk.
        '''
        self.walk = W
        Function.__init__(
                self, EdgeSequence._operator_, W, styles=styles)


class EdgeSet(Function):
    '''
    Given a walk W in Walks(k, G) consisting of vertex sequence S in
    graph G, EdgeSet(W) represents the set (not the sequence) of edges
    traveled along the walk, which for a simple graph is completely
    determined by the vertex sequence S. The sequence of edges traveled
    in the walk W, represented by EdgeSequence(W), will have the same
    edges as EdgeSet(W), but EdgeSequence(W) might have repeated
    edges.
    '''

    # the literal operator of the EdgeSet operation
    _operator_ = Literal(string_format='EdgeSet',
                         latex_format=r'\mathrm{EdgeSet}',
                         theory=__file__)

    def __init__(self, W, *, styles=None):
        '''
        Given a walk W = Walk(S, G) in graph G, represent the
        set of edges traveled during the walk.
        '''
        self.walk = W
        Function.__init__(
                self, EdgeSet._operator_, W, styles=styles)


class EndVertices(Function):
    '''
    EndVertices(W) represents the set of endvertices or endpoints of
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

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [EndVertices(W)], deduce and return
        the equality:
            [EndVertices(W)]
             = {BeginningVertex(W) = EndingVertex(W)}
        '''
        from . import endvertices_def
        from proveit import k, G, W
        from proveit.graphs import WalkLength
        _W_sub  = self.operand
        _k_sub  = WalkLength(self.operand)
        # _G_sub  = _W_sub.graph

        return endvertices_def.instantiate(
                {k: _k_sub, W: _W_sub, G:G },auto_simplify=False)


class BeginningVertex(Function):
    '''
    BeginningVertex(W) represents the beginning vertex of walk W
    (and recall that trails, paths, circuits, and cycles are all cases
    of walks). Since a length-k walk W is actually a function:
        W:[0,1,...,k] -> Vertices(G),
    BeginningVertex(W) represents the value W(0).
    '''

    # the literal operator of the BeginningVertex(W) operation
    _operator_ = Literal(string_format='BeginningVertex',
                         latex_format=r'\textrm{BeginningVertex}',
                         theory=__file__)

    def __init__(self, W, *, styles=None):
        '''
        Represent BeginningVertex(W), the beginning vertex W(0) of
        walk W in a graph G.
        '''
        self.walk = W
        Function.__init__(
                self, BeginningVertex._operator_, W, styles=styles)


class EndingVertex(Function):
    '''
    EndingVertex(W) represents the ending vertex of walk W (and recall
    that trails, paths, circuits, and cycles are all cases of walks).
    Since a length-k walk W is actually a function:
        W:[0,1,...,k] -> Vertices(G),
    EndingVertex(W) represents the value W(k).
    '''

    # the literal operator of the EndingVertex(W) operation
    _operator_ = Literal(string_format='EndingVertex',
                         latex_format=r'\textrm{EndingVertex}',
                         theory=__file__)

    def __init__(self, W, *, styles=None):
        '''
        Represent EndingVertex(W), the ending vertex W(k) of length-k
        walk W in graph G.
        '''
        self.walk = W
        Function.__init__(
                self, EndingVertex._operator_, W, styles=styles)


class EulerianTrails(Function):
    '''
    EulerianTrails(G) represents the set of Eulerian trails in the
    simple undirected graph G. An Eulerian trail in graph G is a u-v
    walk that uses each and every edge of G exactly once, and such
    an Eulerian trail will exist in G if and only if G is connected
    with exactly two vertices of odd degree. The odd degree vertices
    will then also be the u and v of the u-v walk.
    '''

    # the literal operator of the EulerianTrails operation
    _operator_ = Literal(string_format='EulerianTrails',
                         latex_format=r'\textrm{EulerianTrails}',
                         theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Represent EulerianTrails(G), the set of all Eulerian trails
        in graph G.
        '''
        self.graph = G
        Function.__init__(
                self, EulerianTrails._operator_, G, styles=styles)
