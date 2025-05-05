from proveit import v, P, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership


class EndpointsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set Endpoints(P)
    of the endpoints of path P.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Endpoints(P)], where P is a path (i.e. P
        is an element of the Paths class, or P has been explicitly
        constructed as a Path(V,E) with vertex set V and edge set E),
        deduce and return:
            [elem in Endpoints(P)]
            = [elem in {v | deg(v) <= 1}_{Vertices(P)}],
        where the rhs of that equality is a SetOfAll construction.
        '''

        from . import membership_def
        element = self.element
        _P_sub  = self.domain.path  # or self.domain.operand
        return membership_def.instantiate(
                {v:element, P:_P_sub },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in Endpoints(P)], return:
        [elem in {v | deg(v) <= 1}_{Vertices(P)}],
        i.e. the elem is in the SetOfAll v from Vertices(P) such
        that deg(v) <= 1. 
        The method returns an expression, not a Judgment, and does
        not check that P is actually in the class of Paths.
        '''
        from proveit.logic import InSet, SetOfAll
        from proveit.numbers import one, LessEq
        from proveit.graphs import Degree, Vertices
        element   = self.element
        _domain   = self.domain
        _path     = self.domain.path
        _setofall = SetOfAll(
                v, v, conditions = [LessEq(Degree(v, _path),one)],
                domain = Vertices(_path))
        return InSet(element, _setofall)

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in Endpoints(P)],
        derive and return [elem in {v | deg(v) <= 1}_{Vertices(P)}],
        knowing or assuming self (and that P is a member of the
        class of all Paths).
        '''
        from . import membership_unfolding
        element = self.element
        _P_sub  = self.domain.path  # or self.domain.operand
        return membership_unfolding.instantiate(
                {v:element, P:_P_sub },auto_simplify=False)


class EndpointsNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the set 
    Endpoints(P) of the endpoints of path P.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for EndpointsNonmembership.
        '''
        return
        yield
