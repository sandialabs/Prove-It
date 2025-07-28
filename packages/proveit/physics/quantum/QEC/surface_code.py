from proveit import Function, Literal
from proveit import n


class SurfaceCode(Function):
    '''
    A SurfaceCode expression of the form SurfaceCode(n) denotes
    an n x n Kitaev-style surface code in a standard configuration
    with rough boundaries along the top (north) and bottom (south),
    and smooth boundaries along the right (east) and left (west),
    something like this:
                            * * * * *
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            | | | | |
                            * * * * *
    
    Such a surface code would consist of:

      n^2 + (n-1)^2 data (edge or link) qubits;
      n(n-1) Z plaquette operator, parity, or check qubits;
      n(n-1) X site operator, parity, or check qubits.

    For purposes of analyses of various kinds, we conceptualize the
    rough boundary data qubits as graph edges with end points (shown as
    asterisks in the figure above) at the ends without site operators.
    '''

    # the literal operator of the SurfaceCode operation
    _operator_ = Literal(
            string_format='SC', latex_format=r'SC\!', theory=__file__)

    def __init__(self, n, *, styles=None):
        '''
        Create some SurfaceCode(n), an n x n Kitaev-style surface code.
        '''
        Function.__init__(
                self, SurfaceCode._operator_, n, styles=styles)


class GraphOf(Function):
    '''
    For a given surface code configuration SC of data qubits,
    measurement qubits, and their interconnections, GraphOf(c, SC)
    represents the graph or graph component of the surface code
    component c. For example, for a site operator s in some surface
    code SC, GraphOf(s) represents the corresponding vertex
    in the graph of the surface code. For a data qubit q in the
    surface code, GraphOf(q) represents the corresponding edge in the
    graph of the surface code. For the entire surface code SC,
    GraphOf(C) represents the graph equivalent of the entire structure.
    The graph-equivalent here being conceptualized is based on the
    'merged boundary-points' graph.

    May want to modify name eventually to distinguish two possible
    types of graphical representations (one with merged boundary
    points, one without).

    Some of this conceptualization and wording needs serious work.
    It may also be that we cannot use GraphOf() in this overloaded
    way.
    '''

    # the literal operator for the GraphOf operation
    _operator_ = Literal(
            string_format='graph_of',
            latex_format=r'\mathrm{graph\_of}\!', theory=__file__)

    def __init__(self, c, SC, *, styles=None):
        '''
        Create GraphOf(c, SC), the graph equivalent of the surface code
        structure or code component c in the context of the surface
        code structure SC.
        '''
        Function.__init__(
                self, GraphOf._operator_, (c, SC), styles=styles)


class InteriorVertices(Function):
    '''
    Given a surface code configuration SC, InteriorVertices(E, SC)
    represents the set of interior vertices of the GraphOf(E, SC) in
    the GraphOf(SC, SC). E could be an error acting on or experienced
    by the surface code configuation SC, or it could be a component
    or set of components of the surface code configuration such as
    a specific site or data qubit. InteriorVertices(E, SC) is a
    short-cut for what should actually be
    InteriorVertices(GraphOf(E, SC)).
    The sets InteriorVertices(G) and BoundaryVertices(G) form a
    partition of the set Vertices(G).
    '''

    # the literal operator for the InteriorVertices operation
    _operator_ = Literal(
            string_format='interior_vertices',
            latex_format=r'\mathrm{interior\_vertices}\!', theory=__file__)

    def __init__(self, E, SC, *, styles=None):
        '''
        Create InteriorVertices(E, SC), the set of interior vertices
        associated with error or surface code component E in the
        context of the surface code configuration SC.
        '''
        Function.__init__(
                self, InteriorVertices._operator_, (E, SC), styles=styles)


class BoundaryVertices(Function):
    '''
    Given a surface code configuration SC, BoundaryVertices(E, SC)
    represents the set of boundary vertices of the GraphOf(E, SC) in
    the GraphOf(SC, SC). E could be an error acting on or experienced
    by the surface code configuation SC, or it could be a component
    or set of components of the surface code configuration such as
    a specific site or data qubit. BoundaryVertices(E, SC) is a
    short-cut for what should actually be
    BoundaryVertices(GraphOf(E, SC)).
    The sets InteriorVertices(G) and BoundaryVertices(G) form a
    partition of the set Vertices(G).
    '''

    # the literal operator for the InteriorVertices operation
    _operator_ = Literal(
            string_format='boundary_vertices',
            latex_format=r'\mathrm{boundary\_vertices}\!', theory=__file__)

    def __init__(self, E, SC, *, styles=None):
        '''
        Create BoundaryVertices(E, SC), the set of bunodary vertices
        associated with error or surface code component E in the
        context of the surface code configuration SC.
        '''
        Function.__init__(
                self, BoundaryVertices._operator_, (E, SC), styles=styles)


class SiteSyndrome(Function):
    '''
    Let E be an error, conceptualized as an element of the Pauli group
    G_{n}, acting on or experienced by some surface code configuration
    C. Then SiteSyndrome(E) represents the set of X checks or site
    operators that signal one or more errors in the surface code
    (i.e., the set of X site checks that “flip state” as a result of
    the given error E).
    '''

    # the literal operator for the SiteSyndrome operation
    _operator_ = Literal(
            string_format='site_syndrome',
            latex_format=r'\mathrm{site\_syndrome}\!', theory=__file__)

    def __init__(self, E, SC, *, styles=None):
        '''
        Create SiteSyndrome(E, SC), the 'site syndrome' or set of X
        checks signaling errors detected in the surface code SC in
        response to the error E.
        '''
        Function.__init__(
                self, SiteSyndrome._operator_, (E, SC), styles=styles)


class LogicalHadamard(Function):
    '''
    LogicalHadamard(i, SC(n)) represents the surface code configuration
    resulting from the ith step (0 <= i <= n) of a logical Hadamard
    (as defined in Dennis, Kitaev, Landahl, & Preskill's (2002)
    Topological Quantum Memory, particularly Fig. 19 and description
    on pp 4496-4497) acting on a logical qubit represented by the
    surface code SC(n).
    In this representation, we take the 0th step to consist of the
    application of Hadamards to each individual data qubit (resulting
    in a functional exchange of the plaquette and site operator qubits).
    Steps 1, 2, ..., n consist of the accretion/ deletion steps that
    produce the virtual rotation of the logical qubit.
    '''

    # the literal operator of the LogicalHadamard, H_{L}, operation
    _operator_ = Literal(
            string_format='H_L', latex_format=r'H\!_{L}', theory=__file__)

    def __init__(self, i, surface_code, *, styles=None):
        '''
        Create an expression representing the result of the ith step
        of a logical Hadamard acting on an n x n surface code
        SurfaceCode(n).
        '''
        Function.__init__(
                self, LogicalHadamard._operator_, (i, surface_code),
                styles=styles)

class RoughBoundaries(Function):
    '''
    RoughBoundaries(SC(n)) represents the set of two subsets of rough
    boundary points associated with the planar surface code SC(n).
    These points don't represent the data qubits themselves but rather
    the non-operator "end points" of the data qubits when the data
    qubits are considered as edges in a Kitaev-style graphical
    representation of the surface code, indicated by the asterisks in
    the figure:
                            * * * * *
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            | | | | |
                            * * * * *

    Rectilinear distances from points in one set to points in the
    other set can then correspond to lengths of operator chains across
    the logical qubit.
    '''
    
    # the literal operator of the RoughBoundaries operation
    _operator_ = Literal(
            string_format='RB', latex_format=r'RB\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing the set of two subsets of
        rough boundary "endpoints" of a given surface code.
        '''
        Function.__init__(
                self, RoughBoundaries._operator_, surface_code,
                styles=styles)


class RoughBoundaryA(Function):
    '''
    RoughBoundaryA(SC(n)) represents one of the two subsets of rough
    boundary points associated with the planar surface code SC(n).
    These points don't represent the data qubits themselves but rather
    the non-operator "end points" of the data qubits when the data
    qubits are considered as edges in a Kitaev-style graphical
    representation of the surface code, indicated by the asterisks in
    the figures (think of the second figure as a 90 deg clockwise
    rotation of the first one):

                A   * * * * *          * - - - - - *
                    |_|_|_|_|             | | | |
                    |_|_|_|_|       B  * - - - - - *  A
                    |_|_|_|_|             | | | |
                    |_|_|_|_|          * - - - - - *
                    | | | | |             | | | |
                B   * * * * *          * - - - - - *
                                          | | | |
                                       * - - - - - *

    RoughBoundaryB() (defined below) represents the other subset of
    rough boundary points. Rectilinear distances from points in one
    set to points in the other set can then correspond to lengths of
    operator chains across the logical qubit.
    '''

    # the literal operator of the RoughBoundaryA operation
    _operator_ = Literal(
            string_format='RBA', latex_format=r'R\!B\!_{A}\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing one of the two subsets of
        rough boundary "endpoints" of a given surface code.
        '''
        Function.__init__(
                self, RoughBoundaryA._operator_, surface_code,
                styles=styles)

class RoughBoundaryB(Function):
    '''
    RoughBoundaryB(SC(n)) represents one of the two subsets of rough
    boundary points associated with the planar surface code SC(n).
    These points don't represent the data qubits themselves but rather
    the non-operator "end points" of the data qubits when the data
    qubits are considered as edges in a Kitaev-style graphical
    representation of the surface code, indicated by the asterisks in
    the figure:
                A   * * * * *          * - - - - - *
                    |_|_|_|_|             | | | |
                    |_|_|_|_|       B  * - - - - - *  A
                    |_|_|_|_|             | | | |
                    |_|_|_|_|          * - - - - - *
                    | | | | |             | | | |
                B   * * * * *          * - - - - - *
                                          | | | |
                                       * - - - - - *

    RoughBoundaryA() (defined above) represents the other subset of
    rough bounday points. Rectilinear distances from points in one
    set to points in the other set can then correspond to lengths of
    operator chains across the logical qubit.
    '''

    # the literal operator of the RoughBoundaryB operation
    _operator_ = Literal(
            string_format='RBB', latex_format=r'R\!B\!_{B}\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing one of the two subsets of
        rough boundary "endpoints" of a given surface code.
        '''
        Function.__init__(
                self, RoughBoundaryB._operator_, surface_code,
                styles=styles)

class SmoothBoundaries(Function):
    '''
    SmoothBoundaries(SC(n)) represents the set of two subsets of smooth
    boundary points associated with the planar surface code SC(n).
    These points don't represent the data qubits themselves but rather
    the non-operator "end points" of the data qubits when the data
    qubits are considered as edges in the dual version of a
    Kitaev-style graphical representation of the surface code,
    indicated by the asterisks in the figure:

        standard:         dual:   * - - - - - *
                                     | | | |
        *|_|_|_|_|*               * - - - - - *
        *|_|_|_|_|*                  | | | | 
        *|_|_|_|_|*               * - - - - - *
        *|_|_|_|_|*                  | | | | 
        *|_|_|_|_|*               * - - - - - *
                                     | | | | 
                                  * - - - - - *

    Rectilinear distances from points in one smooth boundary set to
    points in the other smooth boundary set can then correspond to
    lengths of operator chains across the logical qubit.
    '''
    
    # the literal operator of the SmoothBoundaries operation
    _operator_ = Literal(
            string_format='SB', latex_format=r'SB\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing the set of two subsets of
        smooth boundary "endpoints" of a given surface code.
        '''
        Function.__init__(
                self, SmoothBoundaries._operator_, surface_code,
                styles=styles)


class SmoothBoundaryA(Function):
    '''
    SmoothBoundaryA(SC(n)) represents one of the two subsets (subset
    A in the figures below) of smooth boundary points associated with
    the planar surface code SC(n). These points don't represent the
    data qubits themselves but rather the non-operator "end points" of
    the data qubits when the data qubits are considered as edges in a
    Kitaev-style graphical representation of the surface code,
    indicated by the asterisks in the figures below. The 2nd figure is
    the "dual" representation of the first (where each qubit edge has
    been rotated by 90 degs) and rotating the 2nd figure clockwise by
    90 degs produces the 3rd figure:
                                                    dual rotated
        standard:       dual:   * - - - - - *            A
                                   | | | |           * * * * *
      A *|_|_|_|_|* B         A * - - - - - * B      |_|_|_|_|
        *|_|_|_|_|*                | | | |           |_|_|_|_|
        *|_|_|_|_|*             * - - - - - *        |_|_|_|_|
        *|_|_|_|_|*                | | | |           |_|_|_|_|
        *|_|_|_|_|*             * - - - - - *        | | | | |
                                   | | | |           * * * * *
                                * - - - - - *            B

    SmoothBoundaryB() (representing the points marked B and defined
    below) represents the other subset of smooth boundary points.
    Rectilinear distances from points in set A to points set B (i.e.
    from one smooth boundary to the other) can then correspond to
    lengths of operator chains across the logical qubit.
    '''

    # the literal operator of the SmoothBoundaryA operation
    _operator_ = Literal(
            string_format='SBA', latex_format=r'S\!B\!_{A}\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing one of the two subsets of
        smooth boundary "endpoints" of a given surface code.
        '''
        Function.__init__(
                self, SmoothBoundaryA._operator_, surface_code,
                styles=styles)

class SmoothBoundaryB(Function):
    '''
    SmoothBoundaryB(SC(n)) represents one of the two subsets (subset
    B in the figures below) of smooth boundary points associated with
    the planar surface code SC(n). These points don't represent the
    data qubits themselves but rather the non-operator "end points" of
    the data qubits when the data qubits are considered as edges in a
    Kitaev-style graphical representation of the surface code,
    indicated by the asterisks in the figures below. The 2nd figure is
    the "dual" representation of the first (where each qubit edge has
    been rotated by 90 degs) and rotating the 2nd figure clockwise by
    90 degs produces the 3rd figure:
                                                    dual rotated
        standard:       dual:   * - - - - - *            A
                                   | | | |           * * * * *
      A *|_|_|_|_|* B         A * - - - - - * B      |_|_|_|_|
        *|_|_|_|_|*                | | | |           |_|_|_|_|
        *|_|_|_|_|*             * - - - - - *        |_|_|_|_|
        *|_|_|_|_|*                | | | |           |_|_|_|_|
        *|_|_|_|_|*             * - - - - - *        | | | | |
                                   | | | |           * * * * *
                                * - - - - - *            B

    SmoothBoundaryA() (representing the points marked A and defined
    above) represents the other subset of smooth boundary points.
    Rectilinear distances from points in set A to points set B (i.e.
    from one smooth boundary to the other) can then correspond to
    lengths of operator chains across the logical qubit.
    '''

    # the literal operator of the SmoothBoundaryB operation
    _operator_ = Literal(
            string_format='SBB', latex_format=r'S\!B\!_{B}\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing one of the two subsets of
        smooth boundary "endpoints" of a given surface code.
        '''
        Function.__init__(
                self, SmoothBoundaryB._operator_, surface_code,
                styles=styles)


class ManhattanDistance(Function):
    '''
    ManhattanDistance(p, q) represents the Manhattan distance (also
    known as the L1 distance or more colloquially as the taxi cab
    distance) between points p and q. For 2-D points (x1, y1) and
    (x2, y2), we have:

        ManhattanDistance((x1,y1),(x2,y2)) = |x2-x1| + |y2-y1|
    '''

    # the literal operator of the ManhattanDistance function
    _operator_ = Literal(
            string_format='md', latex_format=r'd_{m}\!', theory=__file__)

    def __init__(self, pt1, pt2, *, styles=None):
        '''
        Create an expression representing the Manhattan or L1 distance
        between two points pt1 and pt2.
        '''
        Function.__init__(
                self, ManhattanDistance._operator_, (pt1, pt2),
                styles=styles)
