import proveit
from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit.logic import Membership
from proveit.numbers.number_sets.number_set import NumberSet
from proveit._common_ import n

class NaturalSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Natural', r'\mathbb{N}', theory=__file__)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.natural_numbers._theorems_ import natural_lower_bound
        return natural_lower_bound.instantiate({n:member}, assumptions=assumptions)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Natural' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduce_member_lower_bound(member, assumptions)
        yield lambda assumptions : self.deduce_member_in_int(member, assumptions)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.natural_numbers._theorems_ import nat_membership_is_bool
        from proveit._common_ import x
        return nat_membership_is_bool.instantiate({x:member}, assumptions=assumptions)

    def deduce_member_in_int(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.integers._theorems_ import nat_within_int
        return nat_within_int.derive_superset_membership(member, assumptions)


class NaturalPosSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'NaturalPos', r'\mathbb{N}^+', theory=__file__)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.natural_numbers._theorems_ import natural_pos_lower_bound
        return natural_pos_lower_bound.instantiate({n:member}, assumptions=assumptions)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in NaturalPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduce_member_lower_bound(member, assumptions)
        yield lambda assumptions : self.deduce_member_in_nat(member, assumptions)
        yield lambda assumptions : self.deduce_member_non_zero(member, assumptions)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.natural_numbers._theorems_ import nat_pos_membership_is_bool
        from proveit._common_ import x
        return nat_pos_membership_is_bool.instantiate({x:member}, assumptions=assumptions)
    
    def deduce_member_in_nat(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.natural_numbers._theorems_ import nat_pos_within_nat
        return nat_pos_within_nat.derive_superset_membership(member, assumptions)

    def deduce_member_non_zero(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.natural_numbers._theorems_ import non_zero_if_is_nat_pos
        _n = non_zero_if_is_nat_pos.instance_param
        return non_zero_if_is_nat_pos.instantiate(
                {_n:member}, assumptions=assumptions)

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from proveit.numbers.number_sets.natural_numbers._theorems_ import nat_pos_within_nat
    from proveit.numbers.number_sets.integers._theorems_ import nat_within_int, nat_pos_within_int

# if proveit.defaults.automation:
#     try:
#         # Import some fundamental theorems without quantifiers that are
#         # imported when automation is used.
#         # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
#         from ._theorems_ import nat_pos_within_nat, nat_within_int, nat_pos_within_int
#     except:
#         pass
