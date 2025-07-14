from proveit import Function, Literal, Operation

class Restriction(Function):
    '''
    Given a function f: A -> B, with domain A and co-domain B,
    and subset S of A, Restriction(f, S) represents the restriction
    of the function f to domain S --- that is, g = Restriction(f, S)
    is a new function such that g(x) = f(x) for all x in S and is
    undefined for x not in S.
    Restriction(f, S) is an element of the set of Functions(S, B).
    The axiomatic definition includes the constraint that S be a
    subset of the original domain A.
    Future work: consider (re-)defining Restriction(f, S) to be
    Restriction(f, A, B, S) so as to explicitly include the original
    domain and co-domain of the function f.
    '''

    # The literal operator for the Restriction function
    # (see further below for actual latex and string implementations).
    _operator_ = Literal('Restriction', r'\textrm{Restriction}',
                         theory=__file__)
    
    def __init__(self, f, domain, *, styles=None):
        # Represent f|_{S}, the restriction of function f: A -> B to
        # the restricted domain S (where S is a subset of A).
        Operation.__init__(
                self, Restriction._operator_, (f, domain), 
                styles=styles)
        self.fxn = f
        self.domain = domain
    
    def latex(self, **kwargs):
        fxn_str = self.fxn.latex(fence=True)
        domain_str = self.domain.latex(fence=True)
        return (fxn_str + r'\vert_{'+ domain_str + r'}')

    def string(self, **kwargs):
        fxn_str    = self.fxn.string(fence=True)
        domain_str = self.domain.string(fence=True)
        return (fxn_str + r'_{' + domain_str + r'}')
