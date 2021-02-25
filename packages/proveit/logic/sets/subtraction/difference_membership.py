from proveit import USE_DEFAULTS
from proveit.logic import Membership, Nonmembership
from proveit import m, x, y, A, B, S

class DifferenceMembership(Membership):
    '''
    Defines methods that apply to membership in a difference set.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Unfold the membership as a side-effect.
        '''
        yield self.unfold
    
    def conclude(self, assumptions=USE_DEFAULTS):
        return self.conclude_as_folded(assumptions)
    
    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Prove something of the form x ∈ (A - B) 
        via (x ∈ A) and (x ∉ B).
        The special case if x in (S - {y}) may be concluded
        via (x ∈ S) and (x ≠ y) as long as that theorem is usable.
        '''
        from . import membership_folding, all_but_one_membership_folding
        from proveit.logic import Set
        _A, _B = self.domain.operands.entries
        if (isinstance(_B, Set) and _B.elements.is_single() and
                all_but_one_membership_folding.is_usable()):
            return all_but_one_membership_folding.instantiate(
                    {x: self.element, S: _A, y: _B.elements[0]},
                    assumptions=assumptions)
        return membership_folding.instantiate(
            {x: self.element, A: _A, B: _B}, assumptions=assumptions)
    
    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return something of the form
        [x ∈ (A - B)] = [(x ∈ A) and (x ∉ B).
        '''
        from . import difference_def
        _A, _B = self.domain.operands.entries
        return difference_def.instantiate(
            {x: self.element, A: _A, B: _B}, assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From something of the form [x ∈ (A - B)], derive and return 
        [(x ∈ A) and (x ∉ B)],
        or, for the special case of
        x in (S - {y}),
        we derive and return 
        [(x ∈ A) and (x ≠ y)]
        (if that theorem is usable).
        '''
        from . import membership_unfolding, all_but_one_membership_unfolding
        from proveit.logic import Set
        _A, _B = self.domain.operands.entries
        if (isinstance(_B, Set) and _B.elements.is_single() and
                all_but_one_membership_unfolding.is_usable()):
            return all_but_one_membership_unfolding.instantiate(
                    {x: self.element, S: _A, y: _B.elements[0]},
                    assumptions=assumptions)
        return membership_unfolding.instantiate(
            {x: self.element, A: _A, B: _B}, assumptions=assumptions)


class DifferenceNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an difference set.
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Unfold the membership as a side-effect.
        '''
        yield self.unfold
    
    def conclude(self, assumptions=USE_DEFAULTS):
        return self.conclude_as_folded(assumptions)
    
    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Prove something of the form x ∉ (A - B) via (x ∉ A) or (x ∈ B).
        The special case if x ∉ (S - {y}) may be concluded
        via (x ∉ S) or (x = y) as long as that theorem is usable.
        '''
        from . import nonmembership_folding, all_but_one_nonmembership_folding
        from proveit.logic import Set
        _A, _B = self.domain.operands.entries
        if (isinstance(_B, Set) and _B.elements.is_single() and
                all_but_one_nonmembership_folding.is_usable()):
            return all_but_one_nonmembership_folding.instantiate(
                    {x: self.element, S: _A, y: _B.elements[0]},
                    assumptions=assumptions)
        return nonmembership_folding.instantiate(
            {x: self.element, A: _A, B: _B}, assumptions=assumptions)

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return something of the form 
        [x ∉ (A - B)] = [(x ∉ A) or (x ∈ B)].
        '''
        from . import nonmembership_equiv
        _A, _B = self.domain.operands.entries
        return nonmembership_equiv.instantiate(
            {x: self.element, A: _A, B: _B}, assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [x ∉ (A - B)], derive and return 
        [(x ∉ A) or (x ∈ B)],
        or, for the special case of x ∈ (S - {y}), we derive and return 
        [(x ∉ A) or (x ∈ y)]
        (if that theorem is usable).
        '''
        from . import (nonmembership_unfolding, 
                       all_but_one_nonmembership_unfolding)
        from proveit.logic import Set
        _A, _B = self.domain.operands.entries
        if (isinstance(_B, Set) and _B.elements.is_single() and
                all_but_one_nonmembership_unfolding.is_usable()):
            return all_but_one_nonmembership_unfolding.instantiate(
                    {x: self.element, S: _A, y: _B.elements[0]},
                    assumptions=assumptions)
        return nonmembership_unfolding.instantiate(
            {x: self.element, A: _A, B: _B}, assumptions=assumptions)
