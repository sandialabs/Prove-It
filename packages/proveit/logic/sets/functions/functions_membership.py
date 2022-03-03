from proveit import prover, equality_prover
from proveit import f, A, B
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

