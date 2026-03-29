from proveit import Literal, Lambda, Function, safe_dummy_vars
from proveit import prover, equality_prover, ClassMembership
from proveit import f, A, B

class IsInjection(ClassMembership):
    '''
    Class membership for injective (one-to-one) functions from a 
    domain to a codomain.
    '''
    _operator_ = Literal('IsInjection', r'\textrm{IsInjection}',
                         theory=__file__)
    
    def __init__(self, func, domain, codomain, *, styles=None):
        ClassMembership.__init__(
            self, IsInjection._operator_, func, domain, codomain, 
            styles=styles)
        self.domain = domain
        self.codomain = codomain

    def formatted_class(self, format_type):
        formatted_domain = self.domain.formatted(format_type, fence=True)
        formatted_codomain = self.codomain.formatted(format_type, fence=True)
        if format_type == 'latex':
            return (r'\left[' + formatted_domain 
                    + r' \xrightarrow[]{\text{1-to-1}} '
                    + formatted_codomain + r'\right]')
        else:
            return ('[' + formatted_domain + r' 1-to-1-> '
                    + formatted_codomain + r']')

    def side_effects(self, judgment):
        '''
        Unfold the injection class membership.
        '''
        yield self.unfold

    @prover
    def conclude(self, **defaults_config):
        '''
        Prove IsInjection(f, A, B)] from
        IsFunction(f, A, B) and ∀_{a, b ∈ A | a ≠ b} f(a) ≠ f(b)
        '''
        from . import membership_folding
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return membership_folding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove that
        IsInjection(f, A, B) =
        IsFunction(f, A, B) and ∀_{a, b ∈ A | a ≠ b} f(a) ≠ f(b)

        for the f, A, and B in correspondence with this
        InjectionsMembership.
        '''
        from . import is_injection_def
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return is_injection_def.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=IsInjection(f, A, B), return
        IsFunction(f, A, B) and ∀_{a, b ∈ A | a ≠ b} f(a) ≠ f(b)
        '''
        from proveit.logic import And, Forall, NotEquals, IsFunction
        _f = self.element
        _A, _B = self.domain, self.codomain
        _a, _b = safe_dummy_vars(2, self.element, self.domain)
        _fa = _f.apply(_a) if isinstance(_f, Lambda) else Function(_f, _a)
        _fb = _f.apply(_b) if isinstance(_f, Lambda) else Function(_f, _b)
        return And(IsFunction(_f, _A, _B),
                   Forall((_a, _b), NotEquals(_fa, _fb), domain=_A,
                          condition=NotEquals(_a, _b)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From IsInjection(f, A, B), derive and return
        IsFunction(f, A, B) and ∀_{a, b ∈ A | a ≠ b} f(a) ≠ f(b)
        '''
        from . import membership_unfolding
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return membership_unfolding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)
