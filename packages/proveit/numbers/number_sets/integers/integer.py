import proveit
from proveit import USE_DEFAULTS
from proveit import a, x
from proveit.numbers.number_sets.number_set import NumberSet


class IntegerSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Integer', r'\mathbb{Z}', theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Integer' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_rational(
                member, assumptions)
        # Added but commented the following out while we debate the
        # wisdom of further side-effects
        # yield lambda assumptions: self.deduce_member_in_real(member, assumptions)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import int_membership_is_bool
        from proveit import x
        return int_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.rational_numbers import int_within_rational
        return int_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import int_within_real
        return int_within_real.derive_superset_membership(
            member, assumptions)


class IntegerNonZeroSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'IntegerNonZero', r'\mathbb{Z}^{\neq 0}', 
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Integer' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_not_zero(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_integer(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_nonzero(
                member, assumptions)
    
    def deduce_member_not_zero(self, member, assumptions=USE_DEFAULTS):
        from . import nonzero_if_in_nonzero_int
        return nonzero_if_in_nonzero_int.instantiate(
            {x: member}, assumptions=assumptions)
    
    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import nonzero_int_membership_is_bool
        from proveit import x
        return nonzero_int_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_integer(self, member, assumptions=USE_DEFAULTS):
        from . import nonzero_int_within_int
        return nonzero_int_within_int.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_rational_nonzero(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.rational_numbers import (
                nonzero_int_within_rational_nonzero)
        return nonzero_int_within_rational_nonzero.derive_superset_membership(
            member, assumptions)


class IntegerNegSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'IntegerNeg', r'\mathbb{Z}^{-}', 
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Integer' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_upper_bound(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_integer(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_integer_non_zero(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_integer_non_pos(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_neg(
                member, assumptions)
    
    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from . import negative_if_in_neg_int
        return negative_if_in_neg_int.instantiate(
            {x: member}, assumptions=assumptions)
    
    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import neg_int_membership_is_bool
        from proveit import x
        return neg_int_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_integer(self, member, assumptions=USE_DEFAULTS):
        from . import neg_int_within_int
        return neg_int_within_int.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_integer_non_zero(self, member, assumptions=USE_DEFAULTS):
        from . import neg_int_within_nonzero_int
        return neg_int_within_nonzero_int.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_integer_non_pos(self, member, assumptions=USE_DEFAULTS):
        from . import neg_int_within_nonpos_int
        return neg_int_within_nonpos_int.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_rational_neg(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.rational_numbers import (
                neg_int_within_rational_neg)
        return neg_int_within_rational_neg.derive_superset_membership(
            member, assumptions)

class IntegerNonPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'IntegerNonPos', r'\mathbb{Z}^{\leq 0}', 
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Integer' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_upper_bound(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_integer(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_nonpos(
                member, assumptions)
    
    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from . import nonpos_if_in_nonpos_int
        return nonpos_if_in_nonpos_int.instantiate(
            {x: member}, assumptions=assumptions)
    
    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import nonpos_int_membership_is_bool
        from proveit import x
        return nonpos_int_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_integer(self, member, assumptions=USE_DEFAULTS):
        from . import nonpos_int_within_int
        return nonpos_int_within_int.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_rational_nonpos(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.rational_numbers import (
                nonpos_int_within_rational_nonpos)
        return nonpos_int_within_rational_nonpos.derive_superset_membership(
            member, assumptions)



if proveit.defaults.automation:
    from . import (nat_within_int,
                   nat_pos_within_int,
                   nat_pos_within_nonzero_int,
                   nonzero_int_within_int,
                   neg_int_within_int, neg_int_within_nonzero_int,
                   neg_int_within_nonpos_int,
                   nonpos_int_within_int)
