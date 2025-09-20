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


class KitaevPlanarSC(Function):
    '''
    KitaevPlanarSC(n, k, d) denotes the set of all Kitaev-style
    planar surface codes utilizing n data qubits to encode k logical
    qubits all with a resulting code distance d.
    As an example, the Kitaev-style planar code with the confuration:

                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            |_|_|_|_|
                            | | | | |

    is an element of the set KitaevPlanarSC(41, 1, 5) of all Kitaev-
    style planar surface codes utilizing 41 data qubits to encode
    1 logical qubit with a code distance of 5.
    '''

    # the literal operator of the KitaevPlanarSC() operation
    _operator_ = Literal(
            string_format='K', latex_format=r'\mathcal{K}\!', theory=__file__)

    def __init__(self, n, k, d, *, styles=None):
        '''
        Denote the set KitaevPlanarSC(n, k, d) of Kitaev-style planar
        surface codes using n data qubits to encode k logical qubits
        with a resulting code distance d.
        '''
        Function.__init__(
                self, KitaevPlanarSC._operator_, (n, k, d), styles=styles)


class Errors(Function):
    '''
    Given some surface code S, Errors(S) is the set of all possible
    errors the surface code might experience. For a surface code
    utilizing n data qubits, Errors(S) is currently conceptualized
    as a special subset of all elements of the Pauli group G_{n},
    consisting of n-tensor-fold Pauli group operators consisting of
    n-fold tensor products of X, Y, Z, and I Pauli operators.
    For example, given a surface code on 4 data qubits, an error
    might look like (X x Y x Z x I) or (Z x I x Z x Z) (where we
    use the small 'x' to indicate a tensor product).
    '''

    # the literal operator of the Errors(S) operation
    _operator_ = Literal(
            string_format='Errors',
            # latex_format=r'\mathrm{Errors}\!',
            latex_format=r'\mathrm{errs}\!',
            theory=__file__)

    def __init__(self, S, *, styles=None):
        '''
        Denote the set Errors(S) of possible errors on the surface
        code S.
        '''
        Function.__init__(
                self, Errors._operator_, S, styles=styles)


class ZErrorChains(Function):
    '''
    For a given surface code S, ZErrorChains(S) is the set of possible
    Z-Error chains on S. Each Z-Error chain can be conceptualized in
    several different ways, all basically equivalent to taking some
    specially-labelled subset of the available data qubits:

    (1) As a chain f: Q -> {0, 1}, assigning to each data qubit q in Q
        a 0-1 label, with 0 interpreted as a Z error to on that qubit,
        and 1 interpreted as the identity operator I appliedto that
        qubit.
    (2) As the set of data qubits experiencing Z errors.
    (3) As a special subset of the data qubits (i.e. the ones then
        experiencing Z errors).
    (4) As an element of the power set of the set of data qubits of S.

    The set ZErrorChains(S) of Z-Error chains on surface code S is a
    subset of Errors(S) of all possible errors on S. For the code-
    capcity model, the cardinality of ZErrorChains(S) is 2^{n}, where
    n is the number of data qubits in the surface code S.
    '''

    # the literal operator of the ZErrorChains(S) operator
    _operator_ = Literal(
            string_format='ZErrorChains',
            latex_format=r'\mathrm{ZErrorChains}\!',
            theory=__file__)

    def __init__(self, S, *, styles=None):
        '''
        Denote the set ZErrorChains(S) of possible Z_error chains
        on the surface code S.
        '''
        Function.__init__(
                self, ZErrorChains._operator_, S, styles=styles)


class SurfaceCodeSiteOps(Function):
    '''
    SurfaceCodeSiteOps(S) is the set of site operators in the
    surface code S (the 'sites' or 'vertices' appearing in the 
    Kitaev-style planar surface code, or the X-site operators
    measuring the parity among Z-errors on neighboring data qubits).
    '''

    # the literal operator of the SurfaceCodeSiteOps(S) operator
    _operator_ = Literal(
            string_format='SiteOps',
            latex_format=r'\mathrm{SiteOps}\!',
            theory=__file__)

    def __init__(self, S, *, styles=None):
        '''
        Denote the set SurfaceCodeSiteOps(S) of all X site operators
        in the surface code S.
        '''
        Function.__init__(
                self, SurfaceCodeSiteOps._operator_, S, styles=styles)


class ZErrorChainSiteOps(Function):
    '''
    ZErrorChainSiteOps(E, S) is the set of site operators associated
    with the ZErrorChain E across the surface code S. Not sure yet if
    we include ALL the site operators, or just the ones that neighbor
    the data qubits with actual Z errors being experienced.
    The printed notation is the same as that used above for the
    SurfaceCodeSiteOps(S).
    '''

    # the literal operator of the ZErrorChainSiteOps(E, S) operator
    _operator_ = Literal(
            string_format='SiteOps',
            latex_format=r'\mathrm{SiteOps}\!',
            theory=__file__)

    def __init__(self, E, S, *, styles=None):
        '''
        Denote the set ZErrorChainSiteOps(E, S) of all X site operators
        associated with the ZErrorChain E across the surface code S.
        '''
        Function.__init__(
                self, ZErrorChainSiteOps._operator_, (E, S), styles=styles)


class SiteOpZErrorCount(Function):
    '''
    SiteOpZErrorCount(s, E, S) represents the number of site operator
    s's data qubits that are experiencing a Z error. This is important
    because the site operator "flips state" or signals an error when
    an odd number of its data qubits experience a Z error.
    '''

    # the literal operator of the SiteOpZErrorCount(s, E, S) operator
    _operator_ = Literal(
            string_format='ZErrCount',
            latex_format=r'\mathrm{ZErrCount}\!',
            theory=__file__)

    def __init__(self, s, E, S, *, styles=None):
        '''
        Denote the number SiteOpZErrorCount(s, E, S) of site operator
        s's data qubits that experience a Z error.
        '''
        Function.__init__(
                self, SiteOpZErrorCount._operator_, (s, E, S),
                styles=styles)


class SiteSyndrome(Function):
    '''
    Let E be an error, conceptualized as an element of the Pauli group
    G_{n}, acting on or experienced by some surface code configuration
    C. Then SiteSyndrome(E, S) represents the set of X checks or site
    operators in surface code S that signal one or more errors in the
    surface code (i.e., the set of X site checks that “flip state” as
    a result of the given error E). SiteSyndrome(E, S) should be a
    (non-strict) subset of SurfaceCodeSiteOps(S) defined elsewhere.
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
