from proveit import prover, equality_prover
from proveit import f, x, fx, A, B
from proveit.logic import SetMembership

class FunctionsMembership(SetMembership):
    '''
    Defines methods that apply to set-theoretic functions (membership
    in a Functions set).
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)
    
    def side_effects(self, judgment):
        '''
        Unfold the injections set membership.
        '''
        yield self.unfold

    @prover
    def conclude(self, **defaults_config):
        '''
        Prove [f ∈ Functions(A, B)] from
        ∀_{a ∈ A} f(a) ∈ B.
        '''
        from . import membership_folding
        functions = self.domain
        _A = functions.domain
        _B = functions.codomain
        _f = self.element
        return membership_folding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove that
        [f in Functions(A, B)] =
        ∀_{a ∈ A} f(a) ∈ B

        for the f, A, and B in correspondence with this
        InjectionsMembership.
        '''
        from . import functions_def
        functions = self.domain
        _A = functions.domain
        _B = functions.codomain
        _f = self.element
        return functions_def.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[f in Functions(A, B)] , return
        ∀_{a ∈ A} f(a) ∈ B
        '''
        from proveit import Function, safe_dummy_var
        from proveit.logic import Forall, InSet
        _f = self.element
        domain = self.domain
        _A, _B = domain.domain, domain.codomain
        _x = safe_dummy_var(self.element, self.domain)
        _fx = Function(_f, _x)
        return Forall(_x, InSet(_fx, _B), domain=_A).readily_provable()

    @prover
    def unfold(self, **defaults_config):
        '''
        From [f in Functions(A, B)], derive and return
        ∀_{a ∈ A} f(a) ∈ B
        '''
        from . import membership_unfolding
        functions = self.domain
        _A = functions.domain
        _B = functions.codomain
        _f = self.element
        return membership_unfolding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

