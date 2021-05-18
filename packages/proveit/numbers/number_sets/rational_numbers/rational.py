import proveit
from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit import q
from proveit.logic import Membership
from proveit.numbers.number_sets.number_set import NumberSet, NumberMembership


class RationalSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Rational', r'\mathbb{Q}',
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .rational_membership import RationalMembership    
        return RationalMembership(element, self)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in Rational' for a given q.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_in_real(member)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_membership_is_bool
        from proveit import x
        return rational_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import rational_within_real
        return rational_within_real.derive_superset_membership(
            member, assumptions)


class RationalNonZeroSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonZero', r'\mathbb{Q}^{\neq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonZeroMembership    
        return RationalNonZeroMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_notzero(member)
        yield lambda: self.deduce_member_in_rational(member)
        yield lambda: self.deduce_member_in_real_nonzero(member)

    def deduce_member_notzero(self, member, assumptions=USE_DEFAULTS):
        from . import nonzero_if_in_rational_nonzero
        return nonzero_if_in_rational_nonzero.instantiate(
            {q: member}, assumptions=assumptions)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonzero_membership_is_bool
        from proveit import x
        return rational_nonzero_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonzero_within_rational
        return rational_nonzero_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_real_nonzero(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonzero_within_real_nonzero)
        return rational_nonzero_within_real_nonzero.derive_superset_membership(
            member, assumptions)


class RationalPosSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalPos', r'\mathbb{Q}^+',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalPosMembership    
        return RationalPosMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_lower_bound(member)
        yield lambda: self.deduce_member_in_rational(member)
        yield lambda: self.deduce_member_in_rational_nonzero(member)
        yield lambda: self.deduce_member_in_rational_nonneg(member)
        yield lambda: self.deduce_member_in_real_pos(member)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from . import positive_if_in_rational_pos
        return positive_if_in_rational_pos.instantiate(
            {q: member}, assumptions=assumptions)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_pos_membership_is_bool
        from proveit import x
        return rational_pos_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        from . import rational_pos_within_rational
        return rational_pos_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_rational_nonzero(self, member, 
                                          assumptions=USE_DEFAULTS):
        from . import rational_pos_within_rational_nonzero
        thm = rational_pos_within_rational_nonzero
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_rational_nonneg(self, member, 
                                         assumptions=USE_DEFAULTS):
        from . import rational_pos_within_rational_nonneg
        thm = rational_pos_within_rational_nonneg
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_real_pos(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_pos_within_real_pos)
        return rational_pos_within_real_pos.derive_superset_membership(
            member, assumptions)


class RationalNegSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNeg', r'\mathbb{Q}^-',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNegMembership    
        return RationalNegMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_upper_bound(member)
        yield lambda: self.deduce_member_in_rational(member)
        yield lambda: self.deduce_member_in_rational_nonzero(member)
        yield lambda: self.deduce_member_in_rational_nonpos(member)
        yield lambda: self.deduce_member_in_rational_nonpos(member)
        yield lambda: self.deduce_member_in_real_neg(member)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from . import negative_if_in_rational_neg
        return negative_if_in_rational_neg.instantiate(
            {q: member}, assumptions=assumptions)    

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_neg_membership_is_bool
        from proveit import x
        return rational_neg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        from . import rational_neg_within_rational
        return rational_neg_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_rational_nonzero(self, member, 
                                          assumptions=USE_DEFAULTS):
        from . import rational_neg_within_rational_nonzero
        thm = rational_neg_within_rational_nonzero
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_rational_nonpos(self, member, 
                                         assumptions=USE_DEFAULTS):
        from . import rational_neg_within_rational_nonpos
        thm = rational_neg_within_rational_nonpos
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_real_neg(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_neg_within_real_neg)
        return rational_neg_within_real_neg.derive_superset_membership(
            member, assumptions)


class RationalNonNegSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonNeg', r'\mathbb{Q}^{\geq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonNegMembership    
        return RationalNonNegMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_lower_bound(member)
        yield lambda: self.deduce_member_in_rational(member)
        yield lambda: self.deduce_member_in_real_nonneg(member)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from . import nonneg_if_in_rational_nonneg
        return nonneg_if_in_rational_nonneg.instantiate(
            {q: member}, assumptions=assumptions)  

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonneg_membership_is_bool
        from proveit import x
        return rational_nonneg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonneg_within_rational
        return rational_nonneg_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_real_nonneg(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonneg_within_real_nonneg)
        return rational_nonneg_within_real_nonneg.derive_superset_membership(
            member, assumptions)


class RationalNonPosSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonPos', r'\mathbb{Q}^{\leq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonPosMembership    
        return RationalNonPosMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_upper_bound(member)
        yield lambda: self.deduce_member_in_rational(member)
        yield lambda: self.deduce_member_in_real_nonpos(member)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from . import nonpos_if_in_rational_nonpos
        return nonpos_if_in_rational_nonpos.instantiate(
            {q: member}, assumptions=assumptions)  

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonpos_membership_is_bool
        from proveit import x
        return rational_nonpos_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonpos_within_rational
        return rational_nonpos_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_real_nonpos(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonpos_within_real_nonpos)
        return rational_nonpos_within_real_nonpos.derive_superset_membership(
            member, assumptions)


if proveit.defaults.automation:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for
    # the first time, but fine after that.
    from . import (nat_within_rational, 
                   int_within_rational,
                   nonzero_int_within_rational_nonzero,
                   nat_within_rational_nonneg,
                   nat_pos_within_rational_pos,
                   neg_int_within_rational_neg,
                   nonpos_int_within_rational_nonpos,
                   rational_nonzero_within_rational,
                   rational_pos_within_rational,
                   rational_neg_within_rational,
                   rational_nonneg_within_rational,
                   rational_nonpos_within_rational,
                   rational_pos_within_rational_nonzero,
                   rational_neg_within_rational_nonzero,
                   rational_pos_within_rational_nonneg,
                   rational_neg_within_rational_nonpos,
                   zero_is_rational)
