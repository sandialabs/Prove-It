from proveit import Literal, Operation, prover
from proveit import a, b, c, d, n, x


class Interval(Operation):
    # operator of the Interval operation.
    _operator_ = Literal(string_format='Interval', theory=__file__)

    r'''
    The Interval class represents a set of of contiguous integers,
    from lower_bound to upper_bound (inclusively). For example:
        Interval(2, 6)
    represents the integer set {2, 3, 4, 5, 6}. Once created, the
    resulting Interval is interpreted as a SET of elements with no
    assurances about the elements being in a particular order.
    '''

    def __init__(self, lower_bound, upper_bound, *, styles=None):
        Operation.__init__(self, Interval._operator_,
                           (lower_bound, upper_bound), styles=styles)
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound

    def string(self, **kwargs):
        return '{' + self.lower_bound.string() + ' .. ' + \
            self.upper_bound.string() + '}'

    def latex(self, **kwargs):
        return r'\{' + self.lower_bound.latex() + r'~\ldotp \ldotp~' + \
            self.upper_bound.latex() + r'\}'

    def membership_object(self, element):
        from .interval_membership import IntervalMembership
        return IntervalMembership(element, self)

    def nonmembership_object(self, element):
        from .interval_membership import IntervalNonmembership
        return IntervalNonmembership(element, self)

    @prover
    def deduce_elem_in_set(self, member, **defaults_config):
        from . import in_interval
        return in_interval.instantiate(
            {a: self.lower_bound, b: self.upper_bound, n: member},
            auto_simplify=False)

    @prover
    def deduce_subset_eq_relation(self, sub_interval, **defaults_config):
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
                {a:_a, b:_b, c:_c, d:_d}, auto_simplify=False)
        else:
            # print("Poop!")
            raise NotImplementedError (
                    "In calling the Interval.deduce_subset_eq_relation() "
                    "method, the proposed subset {} needs to be an Interval.".
                    format(sub_interval))

