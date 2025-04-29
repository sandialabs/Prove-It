from proveit import Function, Literal

class Endpoints(Function):
    '''
    Endpoints(P) denotes the set of two endpoints of a Path P = (V, E),
    where Path P has vertex set V and edge set E. Endpoints(P) will be
    a subset of the Path P's vertex set V, and for a non-trivial path
    consisting of more than one vertex will consist of the 1-degree
    vertices.
    Endpoints(P) will not "know" the original path P whence it came.
    '''

    # the literal operator of the Endpoints operator
    _operator_ = Literal(
            string_format='Endpts', latex_format=r'\mathrm{Endpts}',
            theory=__file__)

    def __init__(self, P, *, styles=None):
        '''
        Create the endpoints set EndPts(P) for Path P.
        '''
        Function.__init__(
                self, Endpoints._operator_, P, styles=styles)

    def membership_object(self, element):
        from .endpoints_membership import EndpointsMembership
        return EndpointsMembership(element, self)

    def nonmembership_object(self, element):
        from .endpoints_membership import EndpointsNonmembership
        return EndpointsNonmembership(element, self)