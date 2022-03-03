from proveit import Judgment, Lambda, Conditional, prover, equality_prover
from proveit import f, g, x, A, B, C
from proveit.logic import InSet, SetMembership
from .bijections import Bijections

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
        if (isinstance(self.element, Lambda) and 
                isinstance(self.element.body, Conditional) and
                self.element.body.condition == InSet(self.element.parameter,
                                                     self.domain.domain)):
            # From [(x -> f(x) if x ∈ A) ∈ Bijections(A, B)], 
            # derive and return [f ∈ Bijections(A, B)].
            yield self.elim_domain_condition

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
    
    @prover
    def elim_domain_condition(self, **defaults_config):
        '''
        From [(x -> f(x) if x ∈ A) ∈ Bijections(A, B)], 
        derive and return
        [f ∈ Bijections(A, B)].
        '''
        from . import elim_domain_condition
        bijections = self.domain
        _A = bijections.domain
        _B = bijections.codomain
        _f_with_cond = self.element
        if (not isinstance(_f_with_cond, Lambda) or 
                not isinstance(_f_with_cond.body, Conditional)):
            raise TypeError(
                    "'elim_domain_condition' only works with conditioned "
                    "Lambda function element, not %s"%_f_with_cond)
        condition = _f_with_cond.body.condition
        domain_cond = InSet(_f_with_cond.parameter, _A)
        if condition != domain_cond:
            raise TypeError(
                    "'elim_domain_condition' only works with a Lambda "
                    "function element conditioned on the parameter being "
                    "in the domain: %s ≠ %s"%(condition, domain_cond))
        _f = Lambda(_f_with_cond.parameter, _f_with_cond.body.value)
        return elim_domain_condition.instantiate({A:_A, B:_B, f:_f})
    
    @prover
    def apply_transitivity(self, subsequent_bijection,
                           **defaults_config):
        '''
        From [f ∈ Bijections(A, B)] and given [g ∈ Bijections(B, C)]
        [(x -> g(f(x))) ∈ Bijections(A, C)].
        '''
        from . import bijection_transitivity
        if isinstance(subsequent_bijection, Judgment):
            subsequent_bijection = subsequent_bijection.expr
        if not isinstance(subsequent_bijection, InSet):
            raise TypeError(
                    "Expecting 'subsequent_bijection' to be an InSet "
                    "object, got %s"%subsequent_bijection)
        if not isinstance(subsequent_bijection.domain, Bijections):
            raise TypeError(
                    "Expecting 'subsequent_bijection' to represent "
                    "a Bijections membership, got %s"%subsequent_bijection)
        f_codomain = self.domain.codomain
        g_domain = subsequent_bijection.domain.domain
        if f_codomain != g_domain:
            raise TypeError(
                    "Expecting the codomain of %s to match the domain of "
                    "%s"%(self.expr.domain, subsequent_bijection.domain))            
        _f = self.element
        _g = subsequent_bijection.element
        _A = self.domain.domain
        _B = f_codomain
        _C = subsequent_bijection.domain.codomain
        if isinstance(_f, Lambda):
            _x = _f.parameter
        elif isinstance(_g, Lambda):
            _x = _g.parameter
        else:
            _x = x
        return (bijection_transitivity.instantiate(
                {f:_f, g:_g, A:_A, B:_B, C:_C, x:_x})
                .derive_consequent().elim_domain_condition())

