import proveit
from proveit.logic import Equals, NotEquals
from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet


class RealSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Real', r'\mathbb{R}', theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_complex(member,
                                                                assumptions)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import real_membership_is_bool
        return real_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_complex(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.complex_numbers import real_within_complex
        return real_within_complex.derive_superset_membership(
            member, assumptions)


class RealPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealPos', r'\mathbb{R}^+', theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_real(member, assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from . import in_real_pos_iff_positive
        return in_real_pos_iff_positive.instantiate(
            {a: member}, assumptions=assumptions).derive_right_implication(
            assumptions)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import real_pos_membership_is_bool
        from proveit import x
        return real_pos_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from . import real_pos_within_real
        return real_pos_within_real.derive_superset_membership(
            member, assumptions)


class RealNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealNeg', r'\mathbb{R}^-', theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNeg' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_real(member, assumptions)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from . import in_real_neg_iff_negative
        return in_real_neg_iff_negative.instantiate(
            {a: member}, assumptions=assumptions).derive_right_implication(
            assumptions)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import real_neg_membership_is_bool
        from proveit import x
        return real_neg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from . import real_neg_within_real
        return real_neg_within_real.derive_superset_membership(
            member, assumptions)


class RealNonNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'RealNonNeg', r'\mathbb{R}^{\ge 0}',
                           theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonNeg' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_real(member, assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from . import in_real_non_neg_iff_non_negative
        return in_real_non_neg_iff_non_negative.instantiate(
            {a: member}, assumptions=assumptions).derive_right_implication(
            assumptions)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import real_non_neg_membership_is_bool
        from proveit import x
        return real_non_neg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from . import real_non_neg_within_real
        return real_non_neg_within_real.derive_superset_membership(
            member, assumptions)

# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from . import (
#         real_pos_within_real, real_neg_within_real, real_non_neg_within_real, int_within_real,
#         nat_within_real, nat_pos_within_real, nat_pos_within_real_pos)


if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    try:
        # This can fails before running the _axioms_ and _theorems_
        # notebooks for the first time, but fine after that.
        from . import (
            real_pos_within_real,
            real_neg_within_real,
            real_non_neg_within_real,
            rational_within_real,
            int_within_real,
            nat_within_real,
            nat_pos_within_real,
            nat_pos_within_real_pos,
            nat_within_real_non_neg,
            nat_pos_within_real_non_neg,
            real_pos_within_real_non_neg)
    except BaseException:
        pass
