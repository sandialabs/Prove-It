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

    def as_defined(self):
        '''
        From self=[f ∈ Injections(A, B)] , return
        ([f ∈ Functions(A, B)] and
         forall_{a, b ∈ A | a ≠ b} f(a) ≠ f(b))
        '''
        from proveit import Lambda, Function, safe_dummy_vars
        from proveit.logic import Functions
        from proveit.logic import And, Forall, NotEquals, InSet
        _f = self.element
        domain = self.domain
        _A, _B = domain.domain, domain.codomain
        _a, _b = safe_dummy_vars(2, self.element, self.domain)
        _fa = _f.apply(_a) if isinstance(_f, Lambda) else Function(_f, _a)
        _fb = _f.apply(_b) if isinstance(_f, Lambda) else Function(_f, _b)
        return And(InSet(_f, Functions(_A, _B)),
                   Forall((_a, _b), NotEquals(_fa, _fb), domain=_A,
                          condition=NotEquals(_a, _b)))

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

