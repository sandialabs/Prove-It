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

class RoughBoundaryA(Function):
    '''
    RoughBoundaryA(SC(n)) represents one of the two subsets of rough
    boundary points associated with the planar surface code SC(n).
    These points don't represent the data qubits themselves but rather
    the non-operator "end points" of the data qubits when the data
    qubits are considered as edges in a Kitaev-style graphical
    representation of the surface code, indicated by the asterisks in
    the figure:
                        A   * * * * *
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            | | | | |
                        B   * * * * *

    RoughBoundaryB() represents the other subset of rough bounday
    points. Rectilinear distances from points in one set to points in
    the other set can then correspond to lengths of operator chains
    across the logical qubit.
    '''

    # the literal operator of the RoughBoundaryA operation
    _operator_ = Literal(
            string_format='RBA', latex_format=r'R\!B\!_{A}\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing the set of two subsets of
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
                        A   * * * * *
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            | | | | |
                        B   * * * * *

    RoughBoundaryA() represents the other subset of rough bounday
    points. Rectilinear distances from points in one set to points in
    the other set can then correspond to lengths of operator chains
    across the logical qubit.
    '''

    # the literal operator of the RoughBoundaryA operation
    _operator_ = Literal(
            string_format='RBB', latex_format=r'R\!B\!_{B}\!', theory=__file__)

    def __init__(self, surface_code, *, styles=None):
        '''
        Create an expression representing the set of two subsets of
        rough boundary "endpoints" of a given surface code.
        '''
        Function.__init__(
                self, RoughBoundaryB._operator_, surface_code,
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
