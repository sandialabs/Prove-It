from proveit import prover
import proveit
from proveit.logic import Equals, NotEquals
from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet


class RealSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Real', r'\mathbb{R}',
                           theory=__file__, styles=styles)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealPos' for a given n.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_in_complex(member)

    @prover
    def deduce_membership_in_bool(self, member, **defaults_config):
        from . import real_membership_is_bool
        return real_membership_is_bool.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_member_in_complex(self, member, **defaults_config):
        from proveit.numbers.number_sets.complex_numbers import real_within_complex
        return real_within_complex.derive_superset_membership(
            member, auto_simplify=False)


class RealNonZeroSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonZero', r'\mathbb{R}^{\neq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonZeroMembership    
        return RealNonZeroMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonZero' for a given n.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_in_real(member)
        yield lambda: self.deduce_member_not_zero(member)
        yield lambda: self.deduce_member_in_complex_nonzero(member)

    @prover
    def deduce_member_not_zero(self, member, **defaults_config):
        from . import nonzero_if_in_real_nonzero
        return nonzero_if_in_real_nonzero.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_membership_in_bool(self, member, **defaults_config):
        from . import real_nonzero_membership_is_bool
        from proveit import x
        return real_nonzero_membership_is_bool.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import real_nonzero_within_real
        return real_nonzero_within_real.derive_superset_membership(
            member, auto_simplify=False)

    @prover
    def deduce_member_in_complex_nonzero(self, member, **defaults_config):
        from proveit.numbers.number_sets.complex_numbers import (
                real_nonzero_within_complex_nonzero)
        return real_nonzero_within_complex_nonzero.derive_superset_membership(
            member, auto_simplify=False)


class RealPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealPos', r'\mathbb{R}^+', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealPosMembership    
        return RealPosMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealPos' for a given n.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_in_real(member)
        yield lambda: self.deduce_member_in_real_nonzero(member)
        yield lambda: self.deduce_member_in_real_nonneg(member)
        yield lambda: self.deduce_member_lower_bound(member)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import positive_if_in_real_pos
        return positive_if_in_real_pos.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_membership_in_bool(self, member, **defaults_config):
        from . import real_pos_membership_is_bool
        from proveit import x
        return real_pos_membership_is_bool.instantiate(
            {x: member}, auto_simplify=False)
    
    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import real_pos_within_real
        return real_pos_within_real.derive_superset_membership(
            member, auto_simplify=False)

    @prover
    def deduce_member_in_real_nonzero(self, member, **defaults_config):
        from . import real_pos_within_real_nonzero
        thm = real_pos_within_real_nonzero
        return thm.derive_superset_membership(member, auto_simplify=False)

    @prover
    def deduce_member_in_real_nonneg(self, member, **defaults_config):
        from . import real_pos_within_real_nonneg
        thm = real_pos_within_real_nonneg
        return thm.derive_superset_membership(member, auto_simplify=False)


class RealNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNeg', r'\mathbb{R}^-', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNegMembership    
        return RealNegMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNeg' for a given n.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_in_real(member)
        yield lambda: self.deduce_member_in_real_nonzero(member)
        yield lambda: self.deduce_member_in_real_nonpos(member)
        yield lambda: self.deduce_member_upper_bound(member)

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import negative_if_in_real_neg
        return negative_if_in_real_neg.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_membership_in_bool(self, member, **defaults_config):
        from . import real_neg_membership_is_bool
        from proveit import x
        return real_neg_membership_is_bool.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import real_neg_within_real
        return real_neg_within_real.derive_superset_membership(
            member, auto_simplify=False)

    @prover
    def deduce_member_in_real_nonzero(self, member, **defaults_config):
        from . import real_neg_within_real_nonzero
        thm = real_neg_within_real_nonzero
        return thm.derive_superset_membership(member, auto_simplify=False)

    @prover
    def deduce_member_in_real_nonpos(self, member, **defaults_config):
        from . import real_neg_within_real_nonpos
        thm = real_neg_within_real_nonpos
        return thm.derive_superset_membership(member, auto_simplify=False)


class RealNonNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonNeg', r'\mathbb{R}^{\ge 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonNegMembership    
        return RealNonNegMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonNeg' for a given n.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_in_real(member)
        yield lambda: self.deduce_member_lower_bound(member)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import nonneg_if_in_real_nonneg
        return nonneg_if_in_real_nonneg.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_membership_in_bool(self, member, **defaults_config):
        from . import real_nonneg_membership_is_bool
        from proveit import x
        return real_nonneg_membership_is_bool.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import real_nonneg_within_real
        return real_nonneg_within_real.derive_superset_membership(
            member, auto_simplify=False)


class RealNonPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonPos', r'\mathbb{R}^{\le 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonPosMembership    
        return RealNonPosMembership(element)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonNeg' for a given n.
        '''
        member = judgment.element
        yield lambda: self.deduce_member_in_real(member)
        yield lambda: self.deduce_member_upper_bound(member)

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import nonpos_if_in_real_nonpos
        return nonpos_if_in_real_nonpos.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_membership_in_bool(self, member, **defaults_config):
        from . import real_nonpos_membership_is_bool
        return real_nonpos_membership_is_bool.instantiate(
            {x: member}, auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import real_nonpos_within_real
        return real_nonpos_within_real.derive_superset_membership(
            member, auto_simplify=False)


if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from . import (
        int_within_real,
        nat_within_real,
        nat_pos_within_real,
        nat_pos_within_real_pos,
        nat_within_real_nonneg,
        nat_pos_within_real_nonneg,
        rational_within_real,
        rational_nonzero_within_real_nonzero,
        rational_pos_within_real_pos,
        rational_neg_within_real_neg,
        rational_nonneg_within_real_nonneg,
        rational_nonpos_within_real_nonpos,
        real_pos_within_real,
        real_pos_within_real_nonzero,
        real_pos_within_real_nonneg,
        real_neg_within_real,
        real_neg_within_real_nonzero,
        real_neg_within_real_nonpos,
        real_nonneg_within_real,
        real_nonpos_within_real)
