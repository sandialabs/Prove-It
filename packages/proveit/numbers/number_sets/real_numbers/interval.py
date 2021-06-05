import proveit
from proveit import Literal, Operation, prover
from proveit import a, b, c, n, x


class RealInterval(Operation):
    r'''
    Base class for all permutations of closed and open intervals.
    Do not construct an object of this class directly!
    Instead, use IntervalOO or IntervalOC etc.
    '''

    def __init__(self, operator, lower_bound, upper_bound, *, styles=None):
        Operation.__init__(self, operator, (lower_bound, upper_bound),
                           styles=styles)
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound


class IntervalOO(RealInterval):
    # operator of the IntervalOO operation.
    _operator_ = Literal(string_format='IntervalOO', theory=__file__)

    def __init__(self, lower_bound, upper_bound, *, styles=None):
        RealInterval.__init__(
            self, IntervalOO._operator_, lower_bound, upper_bound,
            styles=styles)

    def string(self, **kwargs):
        return '(' + self.lower_bound.string() + \
            ',' + self.upper_bound.string() + ')'

    def latex(self, **kwargs):
        return (r'\left(' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right)')

    def membership_object(self, element):
        from .real_interval_membership import IntervalOOMembership
        return IntervalOOMembership(element, self)

    def nonmembership_object(self, element):
        from .real_interval_membership import RealIntervalNonmembership
        return RealIntervalNonmembership(element, self)

    @prover
    def deduce_elem_in_set(self, member, **defaults_config):
        from . import in_IntervalOO
        return in_IntervalOO.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import interval_oo_lower_bound
        return interval_oo_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import interval_oo_upper_bound
        return interval_oo_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import all_in_interval_oo__is__real
        return all_in_interval_oo__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_rescaled_membership(self, member, scale_factor,
                                   **defaults_config):
        from . import rescale_interval_oo_membership
        return rescale_interval_oo_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, 
             x: member}) # auto-simplification possible

    @prover
    def deduce_left_relaxed_membership(self, member, **defaults_config):
        from . import relax_IntervalOO_left
        return relax_IntervalOO_left.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_right_relaxed_membership(
            self, member, **defaults_config):
        from . import relax_IntervalOO_right
        return relax_IntervalOO_right.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_fully_relaxed_membership(self, member,
                                        **defaults_config):
        from . import relax_IntervalOO_left_right
        return relax_IntervalOO_left_right.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)


class IntervalOC(RealInterval):
    # operator of the IntervalOC operation.
    _operator_ = Literal(string_format='IntervalOC', theory=__file__)

    def __init__(self, lower_bound, upper_bound, *, styles=None):
        RealInterval.__init__(
            self, IntervalOC._operator_, lower_bound, upper_bound,
            styles=styles)

    def string(self, **kwargs):
        return '(' + self.lower_bound.string() + \
            ',' + self.upper_bound.string() + ']'

    def latex(self, **kwargs):
        return (r'\left(' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right]')

    def membership_object(self, element):
        from .real_interval_membership import IntervalOCMembership
        return IntervalOCMembership(element, self)

    def nonmembership_object(self, element):
        from .real_interval_membership import RealIntervalNonmembership
        return RealIntervalNonmembership(element, self)

    @prover
    def deduce_elem_in_set(self, member, **defaults_config):
        from . import in_IntervalOC
        return in_IntervalOC.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import interval_oc_lower_bound
        return interval_oc_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import interval_oc_upper_bound
        return interval_oc_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import all_in_interval_oc__is__real
        return all_in_interval_oc__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_rescaled_membership(self, member, scale_factor,
                                   **defaults_config):
        from . import rescale_interval_oc_membership
        return rescale_interval_oc_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, 
             x: member}) # auto-simplification possible

    @prover
    def deduce_relaxed_membership(self, member, **defaults_config):
        from . import relax_IntervalOC
        return relax_IntervalOC.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_left_relaxed_membership(self, member, **defaults_config):
        return self.deduce_relaxed_membership(member)


class IntervalCO(RealInterval):
    # operator of the IntervalCO operation.
    _operator_ = Literal(string_format='IntervalCO', theory=__file__)

    def __init__(self, lower_bound, upper_bound, *, styles=None):
        RealInterval.__init__(
            self, IntervalCO._operator_, lower_bound, upper_bound,
            styles=styles)

    def string(self, **kwargs):
        return '[' + self.lower_bound.string() + ',' + \
            self.upper_bound.string() + ')'

    def latex(self, **kwargs):
        return (r'\left[' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right)')

    def membership_object(self, element):
        from .real_interval_membership import IntervalCOMembership
        return IntervalCOMembership(element, self)

    def nonmembership_object(self, element):
        from .real_interval_membership import RealIntervalNonmembership
        return RealIntervalNonmembership(element, self)

    @prover
    def deduce_elem_in_set(self, member, **defaults_config):
        from . import in_IntervalCO
        return in_IntervalCO.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import interval_co_lower_bound
        return interval_co_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import interval_co_upper_bound
        return interval_co_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import all_in_interval_co__is__real
        return all_in_interval_co__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_rescaled_membership(self, member, scale_factor,
                                   **defaults_config):
        from . import rescale_interval_co_membership
        return rescale_interval_co_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, 
             x: member}) # auto-simplification possible

    @prover
    def deduce_relaxed_membership(self, member, **defaults_config):
        from . import relax_IntervalCO
        return relax_IntervalCO.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_right_relaxed_membership(self, member, **defaults_config):
        return self.deduce_relaxed_membership(member)


class IntervalCC(RealInterval):
    # operator of the IntervalCC operation.
    _operator_ = Literal(string_format='IntervalCC', theory=__file__)

    def __init__(self, lower_bound, upper_bound, *, styles=None):
        RealInterval.__init__(
            self, IntervalCC._operator_, lower_bound, upper_bound,
            styles=styles)

    def string(self, **kwargs):
        return '[' + self.lower_bound.string() + ',' + \
            self.upper_bound.string() + ']'

    def latex(self, **kwargs):
        return (r'\left[' + self.lower_bound.latex() + ','
                + self.upper_bound.latex() + r'\right]')

    def membership_object(self, element):
        from .real_interval_membership import IntervalCCMembership
        return IntervalCCMembership(element, self)

    def nonmembership_object(self, element):
        from .real_interval_membership import RealIntervalNonmembership
        return RealIntervalNonmembership(element, self)

    @prover
    def deduce_elem_in_set(self, member, **defaults_config):
        from . import in_IntervalCC
        return in_IntervalCC.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import interval_cc_lower_bound
        return interval_cc_lower_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import interval_cc_upper_bound
        return interval_cc_upper_bound.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_member_in_real(self, member, **defaults_config):
        from . import all_in_interval_cc__is__real
        return all_in_interval_cc__is__real.instantiate(
            {a: self.lower_bound, b: self.upper_bound, x: member},
            auto_simplify=False)

    @prover
    def deduce_rescaled_membership(self, member, scale_factor,
                                   **defaults_config):
        from . import rescale_interval_cc_membership
        return rescale_interval_cc_membership.instantiate(
            {a: self.lower_bound, b: self.upper_bound, c: scale_factor, 
             x: member}) # auto-simplification possible
