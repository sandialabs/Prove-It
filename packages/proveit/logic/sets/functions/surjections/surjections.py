from proveit import Function, Literal

class Surjections(Function):
    '''
    A set of functions from a domain to a codomain that are
    one-to-one and onto.
    '''
    _operator_ = Literal('Surjections', r'\textrm{Surjections}',
                         theory=__file__)
    
    def __init__(self, domain, codomain, *, styles=None):
        Function.__init__(self, Surjections._operator_, (domain, codomain), 
                       styles=styles)
        self.domain = domain
        self.codomain = codomain
    
    def latex(self, **kwargs):
        domain_str = self.domain.latex(fence=True)
        codomain_str = self.codomain.latex(fence=True)
        return (r'\left[' + domain_str 
                        + r' \xrightarrow[\text{onto}]{} '
                        + codomain_str + r'\right]')
