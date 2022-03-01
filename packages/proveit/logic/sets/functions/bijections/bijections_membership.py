from proveit import prover, equality_prover
from proveit import f, A, B
from proveit.logic import SetMembership

class BijectionsMembership(SetMembership):
    '''
    Defines methods that apply to bijective functions (membership
    in an Bijections set).
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
        Prove [f ∈ Bijections(A, B)] from
        [f ∈ Injections(A, B)] and
        [f ∈ Surjections(A, B)] 
        '''
        from . import membership_folding
        bijections = self.domain
        _A = bijections.domain
        _B = bijections.codomain
        _f = self.element
        return membership_folding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove that
        [f ∈ Bijections(A, B)] =
        ([f ∈ Injections(A, B)] and
         [f ∈ Surjections(A, B)])

        for the f, A, and B in correspondence with this
        InjectionsMembership.
        '''
        from . import bijective_def
        bijections = self.domain
        _A = bijections.domain
        _B = bijections.codomain
        _f = self.element
        return bijective_def.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)
    @prover
    def unfold(self, **defaults_config):
        '''
        From [f ∈ Bijections(A, B)], derive and return
        [f ∈ Injections(A, B)] and
        [f ∈ Surjections(A, B)].
        '''
        from . import membership_unfolding
        bijections = self.domain
        _A = bijections.domain
        _B = bijections.codomain
        _f = self.element
        return membership_unfolding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

