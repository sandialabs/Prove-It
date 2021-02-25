from proveit import USE_DEFAULTS
from proveit.logic import Membership, Nonmembership
from proveit.numbers import num
from proveit import m, x, A


class IntersectMembership(Membership):
    '''
    Defines methods that apply to membership in an intersection of sets.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set membership as a side-effect.
        '''
        yield self.unfold

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element in (A intersect B ...)] = [(element in A) and (element in B) ...]
        where self = (A intersect B ...).
        '''
        from . import intersection_def
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return intersection_def.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element in (A intersection B ...)], derive and return [(element in A) and (element in B) ...],
        where self represents (A intersection B ...).
        '''
        from . import membership_unfolding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return membership_unfolding.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [element in A], [element in B] ..., derive and return [element in (A intersection B ...)],
        where self represents (A intersection B ...).
        '''
        from . import membership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return membership_folding.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)


class IntersectNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an intersection of sets.
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Currently non side-effects for intersection nonmembership.
        '''
        return
        yield

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return [element not in (A intersect B ...)] = [(element not in A) or (element not in B) ...]
        where self = (A intersect B ...).
        '''
        from . import nonmembership_equiv
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return nonmembership_equiv.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)

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
