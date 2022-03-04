from proveit import Function, Literal

class Bijections(Function):
    '''
    A set of functions from a domain to a codomain that are
    one-to-one and onto.
    '''
    _operator_ = Literal('Bijections', r'\textrm{Bijections}',
                         theory=__file__)
    
    def __init__(self, domain, codomain, *, styles=None):
        Function.__init__(self, Bijections._operator_, (domain, codomain), 
                       styles=styles)
        self.domain = domain
        self.codomain = codomain

    def membership_object(self, element):
        from .bijections_membership import BijectionsMembership
        return BijectionsMembership(element, self)
    
    def latex(self, **kwargs):
        domain_str = self.domain.latex(fence=True)
        codomain_str = self.codomain.latex(fence=True)
        return (r'\left[' + domain_str 
                        + r' \xrightarrow[\text{onto}]{\text{1-to-1}} '
                        + codomain_str + r'\right]')
