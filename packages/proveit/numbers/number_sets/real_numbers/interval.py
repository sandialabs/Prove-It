from proveit import Literal, Operation, USE_DEFAULTS
import proveit._common_
from proveit._common_ import a, b, c, x


class RealInterval(Operation):
    r'''
    Base class for all permutations of closed and open intervals.
    Do not construct an object of this class directly!
    Instead, use IntervalOO or IntervalOC etc.
    '''

    def __init__(self, operator, lower_bound, upper_bound):
        Operation.__init__(self, operator, (lower_bound, upper_bound))
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound


class IntervalOO(RealInterval):
    # operator of the IntervalOO operation.
    _operator_ = Literal(string_format='IntervalOO', theory=__file__)

    def __init__(self, lower_bound, upper_bound):
        RealInterval.__init__(
            self,
            IntervalOO._operator_,
            lower_bound,
            upper_bound)

    def string(self, **kwargs):
        return '(' + self.lower_bound.string() + \
            ',' + self.upper_bound.string() + ')'

    def latex(self, **kwargs):
        return (r'\left(' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right)')

    def deduce_elem_in_set(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalOO
        return in_IntervalOO.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_o_o_lower_bound
        return interval_o_o_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_o_o_upper_bound
        return interval_o_o_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_interval_oo__is__real
        return all_in_interval_oo__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_rescaled_membership(self, member, scale_factor,
                                   assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_interval_oo_membership
        return rescale_interval_oo_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, x: member},
            assumptions=assumptions)

    def deduce_left_relaxed_membership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_left
        return relax_IntervalOO_left.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_right_relaxed_membership(
            self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_right
        return relax_IntervalOO_right.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_left_right_relaxed_membership(self, member,
                                             assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOO_left_right
        return relax_IntervalOO_left_right.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)


class IntervalOC(RealInterval):
    # operator of the IntervalOC operation.
    _operator_ = Literal(string_format='IntervalOC', theory=__file__)

    def __init__(self, lower_bound, upper_bound):
        RealInterval.__init__(
            self,
            IntervalOC._operator_,
            lower_bound,
            upper_bound)

    def string(self, **kwargs):
        return '(' + self.lower_bound.string() + \
            ',' + self.upper_bound.string() + ']'

    def latex(self, **kwargs):
        return (r'\left(' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right]')

    def deduce_elem_in_set(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalOC
        return in_IntervalOC.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_o_c_lower_bound
        return interval_o_c_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_o_c_upper_bound
        return interval_o_c_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_interval_oc__is__real
        return all_in_interval_oc__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_rescaled_membership(self, member, scale_factor,
                                   assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_interval_oc_membership
        return rescale_interval_oc_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, x: member},
            assumptions=assumptions)

    def deduce_relaxed_membership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalOC
        return relax_IntervalOC.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)


class IntervalCO(RealInterval):
    # operator of the IntervalCO operation.
    _operator_ = Literal(string_format='IntervalCO', theory=__file__)

    def __init__(self, lower_bound, upper_bound):
        RealInterval.__init__(
            self,
            IntervalCO._operator_,
            lower_bound,
            upper_bound)

    def string(self, **kwargs):
        return '[' + self.lower_bound.string() + ',' + \
            self.upper_bound.string() + ')'

    def latex(self, **kwargs):
        return (r'\left[' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right)')

    def deduce_elem_in_set(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalCO
        return in_IntervalCO.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_c_o_lower_bound
        return interval_c_o_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_c_o_upper_bound
        return interval_c_o_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_interval_co__is__real
        return all_in_interval_co__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_rescaled_membership(self, member, scale_factor,
                                   assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_interval_co_membership
        return rescale_interval_co_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, x: member},
            assumptions=assumptions)

    def deduce_relaxed_membership(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import relax_IntervalCO
        return relax_IntervalCO.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)


class IntervalCC(RealInterval):
    # operator of the IntervalCC operation.
    _operator_ = Literal(string_format='IntervalCC', theory=__file__)

    def __init__(self, lower_bound, upper_bound):
        RealInterval.__init__(
            self,
            IntervalCC._operator_,
            lower_bound,
            upper_bound)

    def string(self, **kwargs):
        return '[' + self.lower_bound.string() + ',' + \
            self.upper_bound.string() + ']'

    def latex(self, **kwargs):
        return (r'\left[' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right]')

    def deduce_elem_in_set(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import in_IntervalCC
        return in_IntervalCC.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_c_c_lower_bound
        return interval_c_c_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import interval_c_c_upper_bound
        return interval_c_c_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import all_in_interval_cc__is__real
        return all_in_interval_cc__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            assumptions=assumptions)

    def deduce_rescaled_membership(self, member, scale_factor,
                                   assumptions=USE_DEFAULTS):
        from ._theorems_ import rescale_interval_cc_membership
        return rescale_interval_cc_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, x: member},
            assumptions=assumptions)
