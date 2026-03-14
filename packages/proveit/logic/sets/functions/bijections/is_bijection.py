from proveit import Judgment, Literal, Lambda, Conditional
from proveit import prover, equality_prover, ClassMembership
from proveit import f, g, A, B, C

class IsBijection(ClassMembership):
    '''
    Class membership for bijective (one-to-one and onto) functions from a
    domain to a codomain.
    '''
    _operator_ = Literal('IsBijection', r'\textrm{IsBijection}',
                         theory=__file__)
    
    def __init__(self, func, domain, codomain, *, styles=None):
        ClassMembership.__init__(
            self, IsBijection._operator_, func, domain, codomain, 
            styles=styles)
        self.domain = domain
        self.codomain = codomain

    def formatted_class(self, format_type):
        formatted_domain = self.domain.formatted(format_type, fence=True)
        formatted_codomain = self.codomain.formatted(format_type, fence=True)
        if format_type == 'latex':
            return (r'\left[' + formatted_domain 
                    + r' \xrightarrow[\text{onto}]{\text{1-to-1}} '
                    + formatted_codomain + r'\right]')
        else:
            return ('[' + formatted_domain + r' 1-to-1->onto '
                    + formatted_codomain + r']')

    def side_effects(self, judgment):
        '''
        Unfold the bijection class membership.
        '''
        yield self.unfold

    @prover
    def conclude(self, **defaults_config):
        '''
        Prove IsBijection(f, A, B) from
        IsInjection(f, A, B) and
        IsSurjection(f, A, B)
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
        IsBijection(f, A, B) =
        (IsInjection(f, A, B)] and
         [IsSurjection(f, A, B)])

        for the f, A, and B in correspondence with this
        InjectionsMembership.
        '''
        from . import bijective_def
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return bijective_def.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=IsBijection(f, A, B)] , return
        (IsInjection(f, A, B) and IsSurjection(f, A, B))
        '''
        from proveit.logic import And
        from proveit.logic import IsInjection, IsSurjection
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return And(IsInjection(_f, _A, _B),
                   IsSurjection(_f, _A, _B))

    @prover
    def unfold(self, **defaults_config):
        '''
        From IsBijection(f, A, B), derive and return
        IsInjection(f, A, B) and IsSurjection(A, B)].
        '''
        from . import membership_unfolding
        _A = self.domain
        _B = self.codomain
        _f = self.element
        return membership_unfolding.instantiate(
                {A:_A, B:_B, f:_f}, auto_simplify=False)
    
    @prover
    def apply_transitivity(self, subsequent_bijection,
                           **defaults_config):
        '''
        From IsBijection(f, A, B) and given IsBijection(g, B, C), derive
        and return IsBijection(g ∘ f, A, C), derive and return
        '''
        from . import bijection_transitivity
        if isinstance(subsequent_bijection, Judgment):
            subsequent_bijection = subsequent_bijection.expr
        if not isinstance(subsequent_bijection, IsBijection):
            raise TypeError(
                    "Expecting 'subsequent_bijection' to be an "
                    "IsBijection, got %s"%subsequent_bijection)
        f_codomain = self.codomain
        g_domain = subsequent_bijection.domain
        if f_codomain != g_domain:
            raise TypeError(
                    "Expecting the codomain of %s to match the domain of "
                    "%s"%(self.expr, subsequent_bijection))            
        _f = self.element
        _g = subsequent_bijection.element
        _A = self.domain
        _B = f_codomain
        _C = subsequent_bijection.codomain
        return (bijection_transitivity.instantiate(
                {f:_f, g:_g, A:_A, B:_B, C:_C})
                .derive_consequent())