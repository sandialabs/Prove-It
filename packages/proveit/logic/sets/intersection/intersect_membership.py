from proveit import USE_DEFAULTS, equality_prover, prover
from proveit.logic import SetMembership, SetNonmembership
from proveit.numbers import num
from proveit import m, x, A


class IntersectMembership(SetMembership):
    '''
    Defines methods that apply to membership in an intersection of sets.
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
            [element in (A ∩ B ...)] =
            [(element in A) and (element in B) ...]
        where self = [element in (A ∩ B ...)].
        Notice that the self IntersectMembership object need not be
        True for the definition() method to return the equality.
        '''
        from . import intersection_def
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return intersection_def.instantiate({m: _m, x: element, A: _A},
                auto_simplify=False)

    def as_defined(self):
        '''
        From self=[elem in (A ∩ B ∩ ...)], return
        [(element in A) and (element in B) and ...].
        '''
        from proveit.logic import And, InSet
        element = self.element
        return And(*self.domain.operands.map_elements(
                lambda subset : InSet(element, subset)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From [element in (A ∩ B ...)], derive and return
        [(element in A) and (element in B) ...],
        where self represents (A ∩ B ...).
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
        From [element in A], [element in B] ..., (known, proven, or 
        assumed), derive and return [element in (A ∩ B ...)],
        where self represents [element in (A ∩ B ...)].
        '''
        from . import membership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return membership_folding.instantiate(
            {m: _m, x: element, A: _A})


class IntersectNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in an intersection of sets.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently non side-effects for intersection nonmembership.
        '''
        return
        yield

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce and return 
            [element not in (A ∩ B ...)] = 
            [(element not in A) or (element not in B) ...]
        where self = [element not in (A ∩ B ...)].
        '''
        from . import nonmembership_equiv
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return nonmembership_equiv.instantiate(
                {m: _m, x: element, A: _A})

    def as_defined(self):
        '''
        From self=[elem not in (A ∩ B ∩ ...)], return
        [(element not in A) or (element not in B) or ...].
        '''
        from proveit.logic import Or, NotInSet
        element = self.element
        return Or(*self.domain.operands.map_elements(
                lambda subset : NotInSet(element, subset)))

    def _readily_provable(self):
        '''
        Nonmembership in this intersection is readily provable
        iff we can readily disprove the element being in any of the
        intersecting sets.
        '''
        from proveit.logic import NotInSet, any_readily_provable
        return any_readily_provable(
                self.domain.operands,
                lambda subset : NotInSet(self.element, subset))

    @prover
    def conclude(self, **defaults_config):
        '''
        From either [element not in A] or [element not in B] ...
        (already proven or as assumptions), derive and return
        [element not in (A intersection B ...)],
        where self represents [element not in (A intersection B ...)]
        '''
        from . import nonmembership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return nonmembership_folding.instantiate(
            {m: _m, x: element, A: _A})
