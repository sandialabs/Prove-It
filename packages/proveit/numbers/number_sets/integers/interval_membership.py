from proveit import defaults, USE_DEFAULTS, ProofFailure
from proveit import a, b, n, x
from proveit.logic import InSet, Membership, Nonmembership
from proveit.numbers import greater, Less, LessEq
from proveit.numbers import zero, Integer, NaturalPos

class IntervalMembership(Membership):

    '''
    Defines methods that apply to membership in an Interval,
    InSet(x, Interval(m, n), where Interval(m, n) represents a set
    of contiguous integers of the form {m, m+1, m+2, ..., n}.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        As possible side-effects:
        (1) Unfold the Interval set membership:
            (a) deduce elem in Integers (assuming we know upper and
                lower bounds are integers);
            (b) deduce lower_bound <= elem
            (c) deduce elem <= upper_bound
        (2) Deduce that the membership claim is Boolean
        (3) Try to deduce element in more restrictive subset of Integer
        '''
        yield self.deduce_element_in_integer
        yield self.deduce_element_lower_bound
        yield self.deduce_element_upper_bound
        yield self.deduce_in_bool
        # Temporarily leaving out this checking process until we have
        # access to broader assumptions list
        # if (LessEq(_a, _b).proven(assumptions=assumptions) and
        #     (greater(_a, zero).proven(assumptions=assumptions) or
        #     (InSet(_a, NaturalPos).proven(assumptions=assumptions) and 
        #      InSet(_b, NaturalPos).proven(assumptions=assumptions)) )):
        #     yield self.deduce_element_in_restricted_number_set
        yield self.deduce_element_in_restricted_number_set

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [element in Integer] and [lower_bound <= element] and
        [element <= upper_bound], derive and return
        [element in Interval(lower_bound, upper_bound)]
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checked_assumptions(assumptions)

        from proveit import ProofFailure
        from . import in_interval
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element
        return in_interval.instantiate(
                {a: _a, b: _b, n: _n}, assumptions=assumptions)

    # def unfold(self, assumptions=USE_DEFAULTS):
    #     '''
    #     From [element in Interval(x, y)], derive and return the following
    #     3 properties:
    #     (1) element in Integer
    #     (2) x <= element
    #     (3) element <= y
    #     [(element=x) or (element=y) or ..].
    #     From original EnumMembership class:
    #     From [element in {x, y, ..}], derive and return
    #     [(element=x) or (element=y) or ..]
    #     '''
    #     from . import unfold_singleton, unfold
    #     enum_elements = self.domain.elements
    #     if enum_elements.is_single():
    #         return unfold_singleton.instantiate(
    #             {x: self.element, y: enum_elements[0]}, assumptions=assumptions)
    #     else:
    #         _y = enum_elements
    #         _n = _y.num_elements(assumptions=assumptions)
    #         return unfold.instantiate({n: _n, x: self.element, y: _y}, 
    #                                   assumptions=assumptions)
    
    def deduce_element_in_integer(self, assumptions=USE_DEFAULTS):
        '''
        from (element in Interval(x, y)), deduce (element in Integer)
        '''
        from . import interval_is_int
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element
        return interval_is_int.instantiate(
            {a: _a, b: _b, n: _n}, assumptions=assumptions)

    def deduce_element_lower_bound(self, assumptions=USE_DEFAULTS):
        from . import interval_lower_bound
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element
        return interval_lower_bound.instantiate(
            {a: _a, b: _b, n: _n}, assumptions=assumptions)

    def deduce_element_upper_bound(self, assumptions=USE_DEFAULTS):
        from . import interval_upper_bound
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element
        return interval_upper_bound.instantiate(
            {a: _a, b: _b, n: _n}, assumptions=assumptions)

    def deduce_element_in_restricted_number_set(self, assumptions=USE_DEFAULTS):
        '''
        from (element in Interval(x, y)), where x and y are already
        known to be in the same further-restricted number_set (for
        example, both are positive integers or both are negative
        integers), deduce that the element is also in that same more
        restrictive set.
        UNDER CONSTRUCTION
        Start by checking most restrictive … 
        '''
        from proveit.numbers import zero, greater, LessEq, NaturalPos

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element

        # Case: lower_bound > 0
        #       so entire Interval is in positive naturals
        if greater(_a, zero).proven(assumptions=assumptions):
          # all elements are positive naturals
          from . import interval_in_nat_pos
          return interval_in_nat_pos.instantiate(
                  {a:_a, b:_b, n:_n}, assumptions=assumptions)

        # Case: lower and upper bounds both in positive naturals,
        #       so again entire Interval is in positive naturals
        if (InSet(_a, NaturalPos).proven(assumptions=assumptions) and 
            InSet(_b, NaturalPos).proven(assumptions=assumptions) and
            LessEq(_a, _b).proven(assumptions=assumptions)):
            from . import all_in_positive_interval_are_natural_pos
            return all_in_positive_interval_are_natural_pos.instantiate(
                    {a: _a, b: _b, n: _n}, assumptions=assumptions)

        # Case: lower and upper bounds both in positive naturals,
        #       so again entire Interval is in positive naturals
        # if (InSet(_a, NaturalPos).proven(assumptions=assumptions) and 
        #     InSet(_b, NaturalPos).proven(assumptions=assumptions)):
        #     from . import all_in_positive_interval_are_natural_pos
        #     return all_in_positive_interval_are_natural_pos.instantiate(
        #             {a: _a, b: _b, n: _n}, assumptions=assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        from . import interval_membership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_membership_is_bool.instantiate(
            {a: _a, b: _b, x: _x}, assumptions=assumptions)


class IntervalNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an Interval(m, n)
    where Interval(m, n) represents a set of contiguous integers.
    of the form {m, m+1, m+2, ..., n}.
    UNDER CONSTRUCTION
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Yield some possible side effects of Interval set nonmembership:
        (1) if element is an integer, deduce some possible bounds on it;
        (2) deduce that the nonmembership claim is Boolean
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        if (InSet(_x, Integer)).proven():
            yield self.deduce_int_element_bounds
        yield self.deduce_in_bool

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From x not in Integers, or an integer x such that x < a or x > b,
        derive and return [element x not in Interval(a, b)],
        where self is the IntervalNonmembership object.
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checked_assumptions(assumptions)

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        from . import not_int_not_in_interval
        try:
            return not_int_not_in_interval.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)
        except ProofFailure:
            from . import int_not_in_interval
            return int_not_in_interval.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

    def deduce_int_element_bounds(self, assumptions=USE_DEFAULTS):
        from . import bounds_for_int_not_in_interval
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return bounds_for_int_not_in_interval.instantiate(
            {a: _a, b: _b, x: _x}, assumptions=assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        from . import interval_nonmembership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_nonmembership_is_bool.instantiate(
            {a: _a, b: _b, x: _x}, assumptions=assumptions)
