from proveit import Operation, Literal

class Functions(Operation):
    '''
    A set of functions from a domain to a codomain.
    '''
    _operator_ = Literal('Functions', r'\textrm{Functions}',
                         theory=__file__)
    
    def __init__(self, domain, codomain, *, styles=None):
        Operation.__init__(self, Functions._operator_, (domain, codomain), 
                       styles=styles)
        self.domain = domain
        self.codomain = codomain
    
    def membership_object(self, element):
        from .functions_membership import FunctionsMembership
        return FunctionsMembership(element, self)
    
    def latex(self, **kwargs):
        domain_str = self.domain.latex(fence=True)
        codomain_str = self.codomain.latex(fence=True)
        return (r'\left[' + domain_str + r' \rightarrow '
                        + codomain_str + r'\right])')

    def string(self, **kwargs):
        domain_str = self.domain.string(fence=True)
        codomain_str = self.codomain.string(fence=True)
        return (r'[' + domain_str + r' -> '
                        + codomain_str + r']')
