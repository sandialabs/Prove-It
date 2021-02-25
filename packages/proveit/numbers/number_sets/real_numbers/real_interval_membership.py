from proveit import defaults, USE_DEFAULTS, ProofFailure
from proveit import a, b, n, x
from proveit.logic import InSet, Membership, Nonmembership, NotInSet
from proveit.numbers import greater, Less, LessEq
from proveit.numbers import zero, Integer, NaturalPos, Real
from proveit.numbers import IntervalOO, IntervalCO, IntervalOC, IntervalCC

class RealIntervalMembership(Membership):

    '''
    Defines methods that apply to membership in a continuous real
    Interval of the form (x, y), [x, y), (x, y], or [x, y], created
    respectively using the classes IntervalOO, IntervalCO, IntervalOC,
    and IntervalCC. Membership in a continuous real interval might then
    appear, for example, as InSet(x, IntervalOO(m, n)) for the claim
    that x lies in the real open interval (m, n).
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        As possible side-effects:
        (1) Unfold the real IntervalXX set membership:
            (a) deduce elem in Real (assuming we know upper and
                lower bounds are Real);
            (b) deduce lower_bound <= elem or lower_bound < elem
            (c) deduce elem <= upper_bound or elem < upper_bound
        (2) Deduce that the membership claim is Boolean
        (3) Try to deduce element in more restrictive subset of Integer
        '''

        yield self.deduce_element_in_real
        yield self.deduce_element_lower_bound
        yield self.deduce_element_upper_bound
        yield self.deduce_in_bool
        # # Temporarily leaving out this checking process until we have
        # # access to broader assumptions list
        # # if (LessEq(_a, _b).proven(assumptions=assumptions) and
        # #     (greater(_a, zero).proven(assumptions=assumptions) or
        # #     (InSet(_a, NaturalPos).proven(assumptions=assumptions) and 
        # #      InSet(_b, NaturalPos).proven(assumptions=assumptions)) )):
        # #     yield self.deduce_element_in_restricted_number_set
        # yield self.deduce_element_in_restricted_number_set

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [element in Real] and [lower_bound <= element] and
        [element <= upper_bound], derive and return
        [element in IntervalCC(lower_bound, upper_bound)] (and
        similarly for strict upper and/or lower bounds).
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checked_assumptions(assumptions)

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # 4 cases corresponding to the 4 types of real intervals
        
        if isinstance(self.domain, IntervalOO):
            from . import in_IntervalOO
            return in_IntervalOO.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCO):
            from . import in_IntervalCO
            return in_IntervalCO.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalOC):
            from . import in_IntervalOC
            return in_IntervalOC.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCC):
            from . import in_IntervalCC
            return in_IntervalCC.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)
    
    def deduce_element_in_real(self, assumptions=USE_DEFAULTS):
        '''
        from (element in IntervalXX(a, b)),
        where XX = OO, CO, OC, or CC,
        and a and b are Real, deduce (element in Real)
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # 4 cases corresponding to the 4 types of real intervals
        
        if isinstance(self.domain, IntervalOO):
            from . import all_in_interval_oo__is__real
            return all_in_interval_oo__is__real.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCO):
            from . import all_in_interval_co__is__real
            return all_in_interval_co__is__real.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalOC):
            from . import all_in_interval_oc__is__real
            return all_in_interval_oc__is__real.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCC):
            from . import all_in_interval_cc__is__real
            return all_in_interval_cc__is__real.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

    def deduce_element_lower_bound(self, assumptions=USE_DEFAULTS):
        '''
        from (element in IntervalXX(a, b)),
        where XX = OO, CO, OC, or CC, and a and b are Real,
        deduce either (a < element) or (a <= element) (depending on
        whether the interval is open or closed on the left-hand side) 
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # 4 cases corresponding to the 4 types of real intervals

        if isinstance(self.domain, IntervalOO):
            from . import interval_o_o_lower_bound
            return interval_o_o_lower_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCO):
            from . import interval_c_o_lower_bound
            return interval_c_o_lower_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalOC):
            from . import interval_o_c_lower_bound
            return interval_o_c_lower_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCC):
            from . import interval_c_c_lower_bound
            return interval_c_c_lower_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

    def deduce_element_upper_bound(self, assumptions=USE_DEFAULTS):
        '''
        from (element in IntervalXX(a, b)),
        where XX = OO, CO, OC, or CC, and a and b are Real,
        deduce either (element < b) or (element <= b) (depending on
        whether the interval is open or closed on the right-hand side)
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # 4 cases corresponding to the 4 types of real intervals

        if isinstance(self.domain, IntervalOO):
            from . import interval_o_o_upper_bound
            return interval_o_o_upper_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCO):
            from . import interval_c_o_upper_bound
            return interval_c_o_upper_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalOC):
            from . import interval_o_c_upper_bound
            return interval_o_c_upper_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCC):
            from . import interval_c_c_upper_bound
            return interval_c_c_upper_bound.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

    def deduce_element_in_restricted_number_set(self, assumptions=USE_DEFAULTS):
        '''
        from (element in IntervalXX(a, b)), where a and b are already
        known to be in the same further-restricted number_set (for
        example, both are positive real or both are negative
        real), deduce that the element is also in that same more
        restrictive set.
        UNDER CONSTRUCTION
        '''
        from proveit.numbers import zero, greater, LessEq, NaturalPos

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element

        # There are some possibly useful cases to consider:
        # (1) IntervalXX(a, b) where a, b > 0. Then elem in pos reals.
        # (2) IntervalXX(a, b) where a, b < 0. Then elem in neg reals.
        # (3) ... where 0 <= a. Then elem is non-negative.
        # Case: lower_bound > 0
        #       so entire Interval is in positive naturals
        # UNDER CONSTRUCTION

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # 4 cases corresponding to the 4 types of real intervals

        if isinstance(self.domain, IntervalOO):
            from . import interval_oo_membership_is_bool
            return interval_oo_membership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCO):
            from . import interval_co_membership_is_bool
            return interval_co_membership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalOC):
            from . import interval_oc_membership_is_bool
            return interval_oc_membership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCC):
            from . import interval_cc_membership_is_bool
            return interval_cc_membership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)


class RealIntervalNonmembership(Nonmembership):
    '''
    UNDER CONSTRUCTION
    Defines methods that apply to non-membership in a continuous real
    Interval of the form (x, y), [x, y), (x, y], or [x, y], created
    respectively using the classes IntervalOO, IntervalCO, IntervalOC,
    and IntervalCC. Non-membership in a continuous real interval might
    then appear, for example, as NotInSet(x, IntervalOO(m, n)) for the
    claim that x does not lie in the real open interval (m, n).
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Yield some possible side effects of real IntervalXX set
        nonmembership:
        (1) If element is real, deduce some possible bounds on it;
        (2) Deduce that the nonmembership claim is Boolean
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        if ((InSet(_x, Real)).proven() and
           (InSet(_x, Real)).proven() and
           (InSet(_x, Real)).proven()):
            yield self.deduce_real_element_bounds
        yield self.deduce_in_bool

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From x not in Real, or a real x such that x < a, x <= a,
        x > b, or x >= b, derive and return
        [element x not in IntervalXX(a, b)],
        where self is the IntervalNonmembership object and XX is
        OO, CO, OC, and/or CC as appropriate.
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checked_assumptions(assumptions)

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # if x not real, then x cannot be in a real interval
        if NotInSet(_x, Real).proven(assumptions=assumptions):

            # 4 cases corresponding to the 4 types of real intervals

            if isinstance(self.domain, IntervalOO):
                from . import not_real_not_in_interval_oo
                return not_real_not_in_interval_oo.instantiate(
                        {a: _a, b: _b, x: _x}, assumptions=assumptions)

            if isinstance(self.domain, IntervalCO):
                from . import not_real_not_in_interval_co
                return not_real_not_in_interval_co.instantiate(
                        {a: _a, b: _b, x: _x}, assumptions=assumptions)

            if isinstance(self.domain, IntervalOC):
                from . import not_real_not_in_interval_oc
                return not_real_not_in_interval_oc.instantiate(
                        {a: _a, b: _b, x: _x}, assumptions=assumptions)

            if isinstance(self.domain, IntervalCC):
                from . import not_real_not_in_interval_cc
                return not_real_not_in_interval_cc.instantiate(
                        {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if (isinstance(self.domain, IntervalOO) and
            (LessEq(_x, _a).proven(assumptions=assumptions) or
             LessEq(_b, _x).proven(assumptions=assumptions))):
            from . import real_not_in_interval_oo
            return real_not_in_interval_oo.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if (isinstance(self.domain, IntervalCO) and
            (Less(_x, _a).proven(assumptions=assumptions) or
             LessEq(_b, _x).proven(assumptions=assumptions))):
            from . import real_not_in_interval_co
            return real_not_in_interval_co.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if (isinstance(self.domain, IntervalOC) and
            (LessEq(_x, _a).proven(assumptions=assumptions) or
             Less(_b, _x).proven(assumptions=assumptions))):
            from . import real_not_in_interval_oc
            return real_not_in_interval_oc.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if (isinstance(self.domain, IntervalCC) and
            (Less(_x, _a).proven(assumptions=assumptions) or
             Less(_b, _x).proven(assumptions=assumptions))):
            from . import real_not_in_interval_cc
            return real_not_in_interval_cc.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        # from . import not_int_not_in_interval
        # try:
        #     return not_int_not_in_interval.instantiate(
        #             {a: _a, b: _b, x: _x}, assumptions=assumptions)
        # except ProofFailure:
        #     from . import int_not_in_interval
        #     return int_not_in_interval.instantiate(
        #             {a: _a, b: _b, x: _x}, assumptions=assumptions)

    # def deduce_int_element_bounds(self, assumptions=USE_DEFAULTS):
    #     from . import bounds_for_int_not_in_interval
    #     _a = self.domain.lower_bound
    #     _b = self.domain.upper_bound
    #     _x = self.element
    #     return bounds_for_int_not_in_interval.instantiate(
    #         {a: _a, b: _b, x: _x}, assumptions=assumptions)

    def deduce_real_element_bounds(self, assumptions=USE_DEFAULTS):
        '''
        From a, b, x all real and NotInSet(x, IntervalXX(a, b)), deduce
        and return that (x <=/< a OR b <=/< x) (where the inequalities
        depend on the the open/closed ends for the interval).
        For example,
        NotInSet(x, IntervalOC(3, 5)).deduce_real_element_bounds()
        should return: Assumptions |- (x <= 3) OR (5 < x).
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # 4 cases corresponding to the 4 types of real intervals

        if isinstance(self.domain, IntervalOO):
            from . import bounds_for_real_not_in_interval_oo
            return bounds_for_real_not_in_interval_oo.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCO):
            from . import bounds_for_real_not_in_interval_co
            return bounds_for_real_not_in_interval_co.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalOC):
            from . import bounds_for_real_not_in_interval_oc
            return bounds_for_real_not_in_interval_oc.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCC):
            from . import bounds_for_real_not_in_interval_cc
            return bounds_for_real_not_in_interval_cc.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that the non-membership claim is Boolean.
        For example, NotInSet(x, IntervalOO(2, 3)).deduce_in_bool()
        should return |- NotInSet(x, IntervalOO(2, 3)) in Bool.
        '''

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # 4 cases corresponding to the 4 types of real intervals

        if isinstance(self.domain, IntervalOO):
            from . import interval_oo_nonmembership_is_bool
            return interval_oo_nonmembership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCO):
            from . import interval_co_nonmembership_is_bool
            return interval_co_nonmembership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalOC):
            from . import interval_oc_nonmembership_is_bool
            return interval_oc_nonmembership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)

        if isinstance(self.domain, IntervalCC):
            from . import interval_cc_nonmembership_is_bool
            return interval_cc_nonmembership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, assumptions=assumptions)
