from proveit import Literal, Lambda, Function, safe_dummy_var
from proveit import prover, equality_prover, ClassMembership
from proveit import f, A, B

class IsFunction(ClassMembership):
    '''
    Class membership for functions from a domain to a codomain.
    '''
    _operator_ = Literal('IsFunction', r'\textrm{IsFunction}',
                         theory=__file__)
    
    def __init__(self, func, domain, codomain, *, styles=None):
        ClassMembership.__init__(
            self, IsFunction._operator_, func, domain, codomain, 
            styles=styles)
        self.domain = domain
        self.codomain = codomain
    
    def formatted_class(self, format_type):
        formatted_domain = self.domain.formatted(format_type, fence=True)
        formatted_codomain = self.codomain.formatted(format_type, fence=True)
        if format_type == 'latex':
            return (r'\left[' + formatted_domain + r' \rightarrow '
                    + formatted_codomain + r'\right]')
        else:
            return ('[' + formatted_domain + r' -> '
                    + formatted_codomain + r']')

    def side_effects(self, judgment):
        '''
        Unfold the injections set membership.
        '''
        yield self.unfold
        
    @prover
    def conclude(self, **defaults_config):
        '''
        Prove [f : [A → B]] from ∀_{a ∈ A} f(a) ∈ B.
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
        [f : [A → B]] = ∀_{a ∈ A} f(a) ∈ B

        for the f, A, and B in correspondence with this
        InjectionsMembership.
        '''
        from . import is_function_def
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return is_function_def.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[f : [A → B]] , return∀_{a ∈ A} f(a) ∈ B
        '''
        from proveit.logic import Forall, InSet
        _A = self.domain
        _B = self.codomain
        _f = self.element
        _x = safe_dummy_var(self.element, self.domain)
        _fx = _f.apply(_x) if isinstance(_f, Lambda) else Function(_f, _x)
        return Forall(_x, InSet(_fx, _B), domain=_A)

    @prover
    def unfold(self, **defaults_config):
        '''
        From [f : [A → B]], derive and return ∀_{a ∈ A} f(a) ∈ B
        '''
        from . import membership_unfolding
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return membership_unfolding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)
