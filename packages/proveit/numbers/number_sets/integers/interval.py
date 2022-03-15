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

    def includes(self, other_set):
        '''
        Return True if this NumberSet includes the 'other_set' set.
        '''
        from proveit.numbers.number_sets.number_set import NumberSet
        return NumberSet.includes(self, other_set)

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

    @prover
    def deduce_cardinality(self, **defaults_config):
        '''
        Deduce and return the equality between Card(self) and algebraic
        expression representing the cardinality (size) of the finite
        contiguous integers Interval set {a..b} in the form
        |- |{a..b}| = b - a + 1.
        For example, given the Interval I = {3..8}, calling
        I.deduce_cardinality returns
        |- |{3..8}| = 6
        (assuming some appropriate auto_simplification of the numeric
        expression 8 - 3 + 1).
        Might have to pre-prove or include as assumptions enough
        information to establish that a and b in Interval(a, b) are
        both integers with a <= b.
        '''
        from . import interval_cardinality
        from proveit.logic.sets import Card
        _a, _b = interval_cardinality.all_instance_params()
        _a_sub = self.lower_bound
        _b_sub = self.upper_bound
        return interval_cardinality.instantiate(
            {_a: _a_sub, _b: _b_sub}, preserve_expr = Card(self))

    @prover
    def deduce_disjointness(self, disjoint_expr, **defaults_config):
        '''
        Prove that two intervals are disjoint sets.
        '''
        from proveit.logic import Disjoint
        from . import disjoint_intervals
        if (not isinstance(disjoint_expr, Disjoint) 
                or not disjoint_expr.sets.is_double()
                or not isinstance(disjoint_expr.sets[0], Interval)
                or not isinstance(disjoint_expr.sets[1], Interval)):
            raise NotImplementedError(
                    "'Interval.deduce_disjointness' only implemented to "
                    "prove that two Intervals are correct, not %s"
                    %disjoint_expr)
        interval1 = disjoint_expr.sets[0]
        interval2 = disjoint_expr.sets[1]
        _a, _b = interval1.operands
        _c, _d = interval2.operands
        return disjoint_intervals.instantiate(
                {a:_a, b:_b, c:_c, d:_d})
