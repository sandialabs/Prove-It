from proveit import Literal, Operation, USE_DEFAULTS
from proveit import a, b, c, d, n


class Interval(Operation):
    # operator of the Interval operation.
    _operator_ = Literal(string_format='Interval', theory=__file__)

    r'''
    Contiguous set of integers, from lower_bound to upper_bound (both bounds to be interpreted inclusively)
    '''

    def __init__(self, lower_bound, upper_bound):
        Operation.__init__(self, Interval._operator_,
                           (lower_bound, upper_bound))
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound

    def string(self, **kwargs):
        return '{' + self.lower_bound.string() + '...' + \
            self.upper_bound.string() + '}'

    def latex(self, **kwargs):
        return r'\{' + self.lower_bound.latex() + r' \dots ' + \
            self.upper_bound.latex() + r'\}'

    def deduce_elem_in_set(self, member):
        from . import in_interval
        return in_interval.instantiate(
            {a: self.lower_bound, b: self.upper_bound, n: member})

    def deduce_member_lower_bound(self, member, assumptions=frozenset()):
        from . import interval_lower_bound
        return interval_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound}).instantiate({n: member})

    def deduce_member_upper_bound(self, member, assumptions=frozenset()):
        from . import interval_upper_bound
        return interval_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound}).instantiate({n: member})

    def deduce_membership(self, element, assumptions=USE_DEFAULTS):
        from . import all_in_interval_InInts, all_in_interval_InNats, all_in_interval_InNatsPos

    def deduce_member_in_integer(self, member, assumptions=frozenset()):
        '''
        edited by JML 7/18/19
        '''
        from . import interval_is_int
        return interval_is_int.instantiate(
            {a: self.lower_bound, b: self.upper_bound}).instantiate({n: member})

    def deduce_member_in_natural(self, member, assumptions=frozenset()):
        from . import all_in_discrete_interval_InNats
        return all_in_discrete_interval_InNats.instantiate(
            {a: self.lower_bound, b: self.upper_bound}).instantiate({n: member})

    def deduce_member_in_natural_pos(self, member, assumptions=frozenset()):
        from . import all_in_discrete_interval_InNatsPos
        return all_in_discrete_interval_InNatsPos.instantiate(
            {a: self.lower_bound, b: self.upper_bound}).instantiate({n: member})

    def deduce_member_is_positive(self, member, assumptions=frozenset()):
        from . import all_in_positive_interval_are_positive
        return all_in_positive_interval_are_positive.instantiate(
            {a: self.lower_bound, b: self.upper_bound}).instantiate({n: member})

    def deduce_member_is_negative(self, member, assumptions=frozenset()):
        from . import all_in_negative_interval_are_negative
        return all_in_negative_interval_are_negative.instantiate(
            {a: self.lower_bound, b: self.upper_bound}).instantiate({n: member})

    def deduce_subset_eq_relation(self, sub_interval, assumptions=USE_DEFAULTS):
        '''
        Deduce that self of the form {a...d} has as a subset_eq the
        Interval of the form {b...c}, if a <= b <= c <= d. Example:
            {1...5}.deduce_subset_eq_relation({2...4})
        should return
            |- {2...4} \subset_eq {1...5}
        Not yet implemented for deducing a ProperSubset relation.
        '''
        if isinstance(sub_interval, Interval):
            from . import interval_subset_eq
            _a = self.lower_bound
            _d = self.upper_bound
            _b = sub_interval.lower_bound
            _c = sub_interval.upper_bound
            return interval_subset_eq.instantiate(
                {a:_a, b:_b, c:_c, d:_d}, assumptions = assumptions)
        else:
            # print("Poop!")
            raise NotImplementedError (
                    "In calling the Interval.deduce_subset_eq_relation() "
                    "method, the proposed subset {} needs to be an Interval.".
                    format(sub_interval))

