from proveit import USE_DEFAULTS, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership
from proveit.numbers import num
from proveit import m, A, x


class UnionMembership(SetMembership):
    '''
    Defines methods that apply to membership in a union of sets.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set membership as a side-effect.
        '''
        yield self.unfold

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce and return 
            [element in (A union B ...)] = 
            [(element in A) or (element in B) ...]
        where self = (A union B ...).
        '''
        from . import union_def
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return union_def.instantiate(
                {m: _m, x: element, A: _A}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem in (A U B U ...)], return
        [(element in A) or (element in B) or ...].
        '''
        from proveit.logic import Or, InSet
        element = self.element
        return Or(*self.domain.operands.map_elements(
                lambda subset : InSet(element, subset)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From [element in (A union B ...)], derive and return
        [(element in A) or (element in B) ...],
        where self represents [element in (A union B ...)].
        '''
        from . import membership_unfolding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return membership_unfolding.instantiate(
            {m: _m, x: element, A: _A}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem in (A U B U ...)], and knowing or
        assuming [[elem in A] OR [elem in B] OR ...], derive and
        return self.
        '''
        from . import membership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return membership_folding.instantiate({m: _m, x: element, A: _A})

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce that self = (elem in (A U B U ... U M)) is in Bool.
        Used as helper function elsewhere and not usually explicitly
        called by the user.
        '''
        from . import union_membership_is_bool
        element = self.element
        operands = self.domain.operands
        _A_sub = operands
        _m_sub = _A_sub.num_elements()
        return union_membership_is_bool.instantiate(
                {m:_m_sub, x:element, A:_A_sub})


class UnionNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in a union of sets.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no side-effects for union nonmembership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self=[elem not in (A U B U ...)], deduce and return
            |- [elem not in (A U B U ...)] = 
            [(element not in A) and (element not in B) and ...].
        '''
        from . import nonmembership_equiv
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return nonmembership_equiv.instantiate(
            {m: _m, x: element, A: _A}, auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem not in (A U B U ...)], return
        [(element not in A) and (element not in B) and ...].
        '''
        from proveit.logic import And, NotInSet
        element = self.element
        return And(*self.domain.operands.map_elements(
                lambda subset : NotInSet(element, subset)))

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on the self = [elem not in (A U B U ...)], from known
        or assumed [element not in A] and [element not in B] ...,
        derive and return self.
        '''
        from . import nonmembership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return nonmembership_folding.instantiate(
            {m: _m, x: element, A: _A})

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce that self = (elem NotIn (A U B U ... U M)) is in Bool.
        Used as helper function elsewhere and not usually explicitly
        called by the user.
        '''
        from . import union_nonmembership_is_bool
        element = self.element
        operands = self.domain.operands
        _A_sub = operands
        _m_sub = _A_sub.num_elements()
        return union_nonmembership_is_bool.instantiate(
                {m:_m_sub, x:element, A:_A_sub})

