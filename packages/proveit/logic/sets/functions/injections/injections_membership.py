from proveit import prover, equality_prover
from proveit import f, A, B
from proveit.logic import SetMembership

class InjectionsMembership(SetMembership):
    '''
    Defines methods that apply to injective functions (membership
    in an Injections set).
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
        Prove [f ∈ Injections(A, B)] from
        [f ∈ Functions(A, B)] and
        forall_{a, b ∈ A | a ≠ b} f(a) ≠ f(b)
        '''
        from . import membership_folding
        injections = self.domain
        _A = injections.domain
        _B = injections.codomain
        _f = self.element
        return membership_folding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove that
        [f ∈ Injections(A, B)] =
        ([f ∈ Functions(A, B)] and
         forall_{a, b ∈ A | a ≠ b} f(a) ≠ f(b))

        for the f, A, and B in correspondence with this
        InjectionsMembership.
        '''
        from . import injective_def
        injections = self.domain
        _A = injections.domain
        _B = injections.codomain
        _f = self.element
        return injective_def.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)
    @prover
    def unfold(self, **defaults_config):
        '''
        From [f ∈ Injections(A, B)], derive and return
        [f ∈ Functions(A, B)] and
        forall_{a, b ∈ A | a ≠ b} f(a) ≠ f(b)
        '''
        from . import membership_unfolding
        injections = self.domain
        _A = injections.domain
        _B = injections.codomain
        _f = self.element
        return membership_unfolding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

