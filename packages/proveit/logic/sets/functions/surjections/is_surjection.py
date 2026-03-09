from proveit import Function, Literal
from proveit import equality_prover, ClassMembership
from proveit import f, A, B

class IsSurjection(ClassMembership):
    '''
    Class membership for surjective (onto) functions from a domain
    to a codomain.
    '''
    _operator_ = Literal('IsSurjection', r'\textrm{IsSurjection}',
                         theory=__file__)
    
    def __init__(self, func, domain, codomain, *, styles=None):
        ClassMembership.__init__(self, IsSurjection._operator_,
                                 func, domain, codomain, styles=styles)
        self.domain = domain
        self.codomain = codomain

    def formatted_class(self, format_type):
        formatted_domain = self.domain.formatted(format_type, fence=True)
        formatted_codomain = self.codomain.formatted(format_type, fence=True)
        if format_type == 'latex':
            return (r'\left[' + formatted_domain 
                    + r' \xrightarrow[\text{onto}]{} '
                    + formatted_codomain + r'\right]')
        else:
            return ('[' + formatted_domain + r' ->onto '
                    + formatted_codomain + r']')

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove that
        IsSurjection(f, A, B) =
        IsFunction(f, A, B) and Image(f, A) = B

        for the f, A, and B in correspondence with this
        InjectionsMembership.
        '''
        from . import surjective_def
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return surjective_def.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=IsSurjection(f, A, B), return
        IsFunction(f, A, B) and Image(f, A) = B
        '''
        from proveit.logic import And, Equals, IsFunction, Image
        _f = self.element
        domain = self.domain
        _A, _B = domain.domain, domain.codomain
        return And(IsFunction(_f, _A, _B), Equals(Image(_f, _A), _B))
