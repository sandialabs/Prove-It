from proveit import Function, Literal


class GraphOf(Function):
    '''
    For a given surface code configuration S of data qubits,
    measurement qubits, and their interconnections, GraphOf(c, S)
    is a generic representation of the graph or graph component of
    the surface code component c with respect to the (again, generic)
    graphical representation of the surface code S. For example,
    for a site operator s in some surface code S, GraphOf(s, S)
    represents the corresponding vertex in the graph of the surface
    code S. For a data qubit q in the surface code, GraphOf(q, S)
    represents the corresponding edge (along with its vertices) in the
    graph of the surface code S. For the entire surface code S,
    GraphOf(S) represents the graph equivalent of the entire structure.
    The very generic graph would promise only that data qubits are
    mapped to graph edges, and site operator qubits mapped to the
    corresponding graph vertices, without specific claims about other
    structural properties of the resulting graph --- for example,
    without claims about there being additional boundary vertices or
    a merging of additional boundary vertices, etc.

    More specific graph representations will generally be needed and
    can be found in the code further below, such as the
    MergedBoundsGraphOfZError(E, S), which represents the graph of
    the error chain E as a subgraph of the merged-boundary-points
    graph of the surface code S.

    This generic GraphOf() function is still under development and may
    be completely replaced eventually by more specific 'graph of'
    functions (such as those below). Even if it continues to exist, we
    may want to modify it eventually to at least distinguish between
    the two possible graphical representations using merged vs.
    unmerged boundary points.
    '''

    # the literal operator for the GraphOf operation
    _operator_ = Literal(
            string_format='graph_of',
            latex_format=r'\mathrm{graph\_of}\!',
            theory=__file__)

    def __init__(self, c, S, *, styles=None):
        '''
        Create GraphOf(c, S), the generic graph equivalent of the
        surface code structure or code component c in the context of
        the graph of the surface code structure S.
        '''
        Function.__init__(
                self, GraphOf._operator_, (c, S), styles=styles)


class MergedBoundsGraphOfSurfaceCode(Function):
    '''
    MergedBoundsGraphOfSurfaceCode(S) represents the graph portrayal
    of the surface code S, where the mapping from surface code S to
    graphical representation is straightforward: each data qubit or
    link in S is mapped to an edge in the graph, and each site or X
    site operator is mapped to a vertex in the graph of S, maintaining
    the site-link connections from the code S. The merged-bounds graph
    of S merges each set of rough boundary points into a single point
    each.
    '''

    # the literal operator for the MergedBoundsGraphOfSurfaceCode()
    # operation
    _operator_ = Literal(
            string_format='mb_graph',
            # latex_format=r'\mathrm{mb\_graph}\!',
            # latex_format=r'\mathcal{G}_{mb}\!',
            latex_format=r'{{\mathcal{G}}_{mb} {\!}}',
            theory=__file__)

    def __init__(self, S, *, styles=None):
        '''
        Represent MergedBoundsGraphOfSurfaceCode(S), the graph of
        surface code S with merged rough boundary points.
        '''
        Function.__init__(
                self, MergedBoundsGraphOfSurfaceCode._operator_, S,
                styles=styles)


class MergedBoundsGraphOfZError(Function):
    '''
    MergedBoundsGraphOfZError(E, S) represents the graph of a Z-error
    chain E with respect to the graph of surface code S, where the
    graph of S merges each set of rough boundary points into a single
    point each, and the graph of the Z-error chain E is a subgraph of
    the graph of S. The mapping from Z-error chain to graph is straight-
    forward, with edges corresponding to data qubits or links in the
    surface code experiencing the Z errors, and vertices in the graph
    corresponding to sites or X site operators connected to those
    Z-error links in the surface code. X-site operator error signals
    are represented implicitly (and automatically) in the graph by
    vertices of odd degree.
    '''

    # the literal operator for the MergedBoundsGraphOfZError() operation
    _operator_ = Literal(
            string_format='mb_graph',
            # latex_format=r'\mathrm{mb\_graph}_{\mathit{zerr}}\!',
            latex_format=r'{{\mathcal{G}}_{mb}{\!}}',
            theory=__file__)

    def __init__(self, E, S, *, styles=None):
        '''
        Represent MergedBoundsGraphOfZError(E, S), the graph of
        Z-error chain E with respect to the merged-boundary-points
        graph of surface code S.
        '''
        Function.__init__(
                self, MergedBoundsGraphOfZError._operator_, (E, S),
                styles=styles)


class InteriorVertices(Function):
    '''
    For a given error chain E on surface code S,
    InteriorVertices(GraphOf(E, S)) represents the set of interior
    (i.e., non-boundary) vertices of the graphical representation
    GraphOf(E, S) of error chain E in the graph of S. The 'GraphOf'
    function here can be any function converting the error chain
    to a graph in the context of the surface code S. In particular,
    the 'GraphOf' fxn could be the MergedBoundsGraphOfZError(E, S).
    Future work may require the development of more targeted versions
    of the InteriorVertices() fxn to distinguish between standard vs.
    merged-boundary-points graphs, and standard vs dual-representation
    graphs.
    The error E would typically be an error chain acting on or
    experienced by the surface code configuation S, or it could be a
    component or set of components of the surface code configuration
    such as a specific site or data qubit.
    Previous work was usuing InteriorVertices(E, S) as a short-cut
    for what should actually be InteriorVertices(GraphOf(E, S)), but
    the 'GraphOf()' fxn is now being considered in multiple ways.
    The sets InteriorVertices(G) and BoundaryVertices(G) are
    conceptualized as forming a partition of the set Vertices(G).
    InteriorVertices(G) and the related BoundaryVertices(G) are
    begin defined here in the QEC package instead of in the graphs
    package because the notions of interior and boundary are different
    from what is commonly considered in graph theory more generally.
    '''

    # the literal operator for the InteriorVertices operation
    _operator_ = Literal(
            string_format='int_verts',
            latex_format=r'\mathrm{int\_verts}\!',
            theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Create InteriorVertices(G), the set of interior vertices
        associated with the graph G of a surface code or error E in
        the context of some surface code.
        '''
        Function.__init__(
                self, InteriorVertices._operator_, G, styles=styles)


class BoundaryVertices(Function):
    '''
    For a given error chain E on surface code S,
    BoundaryVertices(GraphOf(E, S)) represents the set of boundary
    vertices of the graphical representation GraphOf(E, S) of error
    chain E in the graph of S. The 'GraphOf' function here can be any
    function converting the error chain to a graph in the context of
    the surface code S. In particular, the 'GraphOf' fxn could be the
    MergedBoundsGraphOfZError(E, S).
    Future work may require the development of more targeted versions
    of the BoundaryVertices() fxn to distinguish between standard vs.
    merged-boundary-points graphs, and standard vs dual-representation
    graphs.
    Previous work was usuing BoundaryVertices(E, S) as a short-cut
    for what should actually be BoundaryVertices(GraphOf(E, S)), but
    the 'GraphOf()' fxn is now being considered in multiple ways.
    The sets InteriorVertices(G) and BoundaryVertices(G) are
    conceptualized as forming a partition of the set Vertices(G).
    BoundaryVertices(G) and the related InteriorVertices(G) are
    begin defined here in the QEC package instead of in the graphs
    package because the notions of interior and boundary are different
    from what is commonly considered in graph theory more generally.
    '''

    # the literal operator for the InteriorVertices operation
    _operator_ = Literal(
            string_format='bound_verts',
            latex_format=r'\mathrm{bound\_verts}\!', theory=__file__)

    def __init__(self, G, *, styles=None):
        '''
        Create BoundaryVertices(G), the set of boundary vertices
        associated with the graph G of a surface code or error E in
        the context of some surface code.
        '''
        Function.__init__(
                self, BoundaryVertices._operator_, G, styles=styles)

