from proveit import USE_DEFAULTS
from proveit.logic import Membership, Nonmembership
from proveit.numbers import num
from proveit import m, A, x


class UnionMembership(Membership):
    '''
    Defines methods that apply to membership in a unification of sets.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set membership as a side-effect.
        '''
        yield self.unfold

    def equivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element in (A union B ...)] = [(element in A) or (element in B) ...]
        where self = (A union B ...).
        '''
        from . import union_def
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return union_def.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element in (A union B ...)], derive and return [(element in A) or (element in B) ...],
        where self represents (A union B ...).
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
        From either [element in A] or [element in B] ..., derive and return [element in (A union B ...)],
        where self represents (A union B ...).
        '''
        from . import membership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return membership_folding.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)


class UnionNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an unification of sets.
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Currently non side-effects for union nonmembership.
        '''
        return
        yield

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element not in (A union B ...)] = [(element not in A) and (element not in B) ...]
        where self = (A union B ...).
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
        From [element not in A] and [element not in B] ..., derive and return [element not in (A union B ...)],
        where self represents (A union B ...).
        '''
        from . import nonmembership_folding
        element = self.element
        operands = self.domain.operands
        _A = operands
        _m = _A.num_elements(assumptions)
        return nonmembership_folding.instantiate(
            {m: _m, x: element, A: _A}, assumptions=assumptions)
