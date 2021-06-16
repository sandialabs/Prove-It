from proveit import USE_DEFAULTS, equality_prover, prover
from proveit.logic import Membership, Nonmembership
from proveit.numbers import num
from proveit import m, x, A


class IntersectMembership(Membership):
    '''
    Defines methods that apply to membership in an intersection of sets.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set membership as a side-effect.
        '''
        yield self.unfold

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce and return 
            [element in (A intersect B ...)] =
            [(element in A) and (element in B) ...]
        where self = [element in (A intersect B ...)].
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

    @prover
    def unfold(self, **defaults_config):
        '''
        From [element in (A intersection B ...)], derive and return
        [(element in A) and (element in B) ...],
        where self represents (A intersection B ...).
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
        assumed), derive and return [element in (A intersection B ...)],
        where self represents [element in (A intersection B ...)].
        '''
        from . import membership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return membership_folding.instantiate(
            {m: _m, x: element, A: _A})


class IntersectNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an intersection of sets.
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element, domain)

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
            [element not in (A intersect B ...)] = 
            [(element not in A) or (element not in B) ...]
        where self = (A intersect B ...).
        '''
        from . import nonmembership_equiv
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements()
        return nonmembership_equiv.instantiate({m: _m, x: element, A: _A})

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From either [element not in A] or [element not in B] ..., derive and return [element not in (A intersection B ...)],
        where self represents (A intersection B ...).
        '''
        from . import nonmembership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return nonmembership_folding.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)
