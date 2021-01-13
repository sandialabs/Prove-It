from proveit import USE_DEFAULTS
from proveit import a
from proveit.numbers.number_sets.number_set import NumberSet


class IntegerSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Integer', r'\mathbb{Z}', theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Integer' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_rational(member, assumptions)
        # Added but commented the following out while we debate the
        # wisdom of further side-effects
        # yield lambda assumptions: self.deduce_member_in_real(member, assumptions)

    def deduce_in_set_is_bool(self, element, assumptions=USE_DEFAULTS):
        from . import in_ints_is_bool
        return in_ints_is_bool.instantiate(
            {a: element}, assumptions=assumptions)

    def deduce_not_in_set_is_bool(self, element, assumptions=USE_DEFAULTS):
        from . import not_in_ints_is_bool
        return not_in_ints_is_bool.instantiate(
            {a: element}, assumptions=assumptions)

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
