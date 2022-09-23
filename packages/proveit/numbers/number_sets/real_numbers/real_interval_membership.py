from proveit import (defaults, prover, relation_prover,
                     ProofFailure, UnsatisfiedPrerequisites)
from proveit import a, b, n, x
from proveit.logic import InSet, NotInSet, SetNonmembership
from proveit.numbers import (
        Less, LessEq, Real, IntervalOO, IntervalCO, IntervalOC, IntervalCC)
from proveit.numbers.number_sets.number_set import NumberMembership

class RealIntervalMembership(NumberMembership):

    '''
    Defines methods that apply to membership in a continuous real
    Interval of the form (x, y), [x, y), (x, y], or [x, y], created
    respectively using the classes IntervalOO, IntervalCO, IntervalOC,
    and IntervalCC. Membership in a continuous real interval might then
    appear, for example, as InSet(x, IntervalOO(m, n)) for the claim
    that x lies in the real open interval (m, n).
    '''

    def __init__(self, element, domain):
        NumberMembership.__init__(self, element, domain)
        self.domain = domain

    def _readily_provable(self):
        '''
        The Membership is readily provabile if the element
        is readily known to be Real and it's readily known to be 
        within the interval range.
        '''
        from proveit.logic import SubsetEq
        from proveit.numbers import readily_provable_number_set
        domain = self.domain
        _x = self.element
        try:
            elem_ns = readily_provable_number_set(_x)
        except UnsatisfiedPrerequisites:
            elem_ns = None
        if elem_ns is not None:
            if SubsetEq(elem_ns, domain).readily_provable():
                return True
        lb, ub = domain.member_bounds(_x)
        return InSet(_x, Real).readily_provable() and (
                lb.readily_provable() and ub.readily_provable())

    @prover
    def conclude(self, **defaults_config):
        '''
        From [element in Real] and [lower_bound <= element] and
        [element <= upper_bound], derive and return
        [element in IntervalCC(lower_bound, upper_bound)] (and
        similarly for strict upper and/or lower bounds).
        '''
        from proveit.logic import SubsetEq
        from proveit.numbers import (readily_provable_number_set,
                                     deduce_in_number_set)
        domain = self.domain
        element = self.element
        elem_ns = readily_provable_number_set(element)
        if elem_ns == domain:
            return deduce_in_number_set(element, domain)
        sub_rel = SubsetEq(elem_ns, domain)
        if sub_rel.readily_provable():
            return sub_rel.derive_superset_membership(element)
        return domain.deduce_elem_in_set(element)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving x in a real interval for a
        given x.
        (1) Derive elem in Real (assuming we know upper and
            lower bounds are Real);
        (2) Derive lower_bound <= elem or lower_bound < elem
        (3) Derive elem <= upper_bound or elem < upper_bound
        (4) Try to derive element in more restrictive subset of Reals
            with respect to being above or below zero.
        (5) Try to derive the element is in any relaxed intervals
            as appropriate (changing 'open' to 'closed').
        '''
        yield self.derive_element_in_real
        yield self.derive_element_lower_bound
        yield self.derive_element_upper_bound
        yield self.derive_element_in_restricted_number_set_if_known
        if hasattr(self, 'derive_left_relaxed_membership'):
            yield self.derive_left_relaxed_membership
        if hasattr(self, 'derive_right_relaxed_membership'):
            yield self.derive_right_relaxed_membership
        if hasattr(self, 'derive_relaxed_membership'):
            yield self.derive_relaxed_membership
        elif hasattr(self, 'derive_fully_relaxed_membership'):
            yield self.derive_fully_relaxed_membership

    @prover
    def derive_element_in_real(self, **defaults_config):
        '''
        Given the element is in a real interval, prove it is real.
        '''
        return self.domain.deduce_member_in_real(self.element)

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        '''
        Given the element is in a real interval, prove it's lower
        bound.  For example, from x in (2, 10] derive x > 2.
        '''
        return self.domain.deduce_member_lower_bound(self.element)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        '''
        Given the element is in a real interval, prove it's upper
        bound.  For example, from x in (2, 10] derive x ≤ 10.
        '''
        return self.domain.deduce_member_upper_bound(self.element)

    @prover
    def derive_rescaled_membership(self, scale_factor,
                                   **defaults_config):
        '''
        Given the element is in a real interval, prove that the
        rescaled element is in a correspondingly rescaled interval.
        For example, from x in (2, 10] derive 2*x in (4, 20].
        '''
        return self.domain.deduce_rescaled_membership(self.element,
                                                      scale_factor)

    @prover
    def derive_element_in_restricted_number_set_if_known(
            self, **defaults_config):
        '''
        From (element in IntervalXX(x, y)), where either 
        x ≥ 0 or y ≤ 0 is known or provable without automation, 
        derive that the element is in RealPos, RealNeg, RealNonPos, or
        RealNonNeg as appropriate.  If neither x ≥ 0 nor y ≤ 0 is 
        known or provable without automation, raise an
        UnsatisfiedPrerequisites exception.
        '''
        from proveit.numbers import RealNonNeg, RealNonPos
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        if (InSet(_a, RealNonNeg).readily_provable() or 
                InSet(_b, RealNonPos).readily_provable()):
            return self.derive_element_in_restricted_number_set()
        if (InSet(_a, RealNonNeg).readily_provable() or 
                InSet(_b, RealNonPos).readily_provable()):
            return self.derive_element_in_restricted_number_set()
        raise UnsatisfiedPrerequisites(
                "Must know that the lower bound is non-negative or the "
                "upper bound is non-positive to perform "
                "derive_element_in_restricted_number_set_if_known")

    @prover
    def derive_element_in_restricted_number_set(self, **defaults_config):
        '''
        From (element in IntervalXX(x, y)), where x ≥ 0 or y ≤ 0,
        derive that the element is in RealPos, RealNeg, RealNonPos, or
        RealNonNeg as appropriate.
        '''
        from proveit.numbers import (zero, RealPos, RealNonNeg, 
                                     RealNeg, RealNonPos)
        from proveit.numbers import Less, LessEq, greater, greater_eq        
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element
        
        # We wish to deduce a fact based upon the following
        # membership fact:
        self.expr.prove()

        if (not InSet(_a, RealNonNeg).readily_provable() and 
                not InSet(_b, RealNonPos).readily_provable()):
            # If we don't know that a ≥ 0 or b ≤ 0, we can't prove
            # the element is in either restricted number set
            # (NaturalPos or IntegerNeg).  So, try to sort a, b, 0
            # to work this out.
            LessEq.sort([_a, _b, zero])

        if InSet(_a, RealNonNeg).readily_provable():
            lower_bound = self.derive_element_lower_bound()
            a_bound = greater_eq(_a, zero)
            if InSet(_a, RealPos).readily_provable():
                a_bound = greater(_a, zero)
            lower_bound.apply_transitivity(a_bound)
            if (isinstance(self, IntervalOO) 
                    or isinstance(self, IntervalOC)
                    or InSet(_a, RealPos).readily_provable()):
                # member in R^{>0}
                return InSet(_n, RealPos).prove()
            else:
                # member in R^{≥0}
                return InSet(_n, RealNonNeg).prove()
        if InSet(_b, RealNonPos).readily_provable():
            try:
                _b.deduce_in_number_set(RealNeg, automation=False)
            except Exception:
                pass
            upper_bound = self.derive_element_upper_bound()
            b_bound = LessEq(_b, zero)
            if InSet(_b, RealNeg).readily_provable():
                b_bound = Less(_b, zero)                
            upper_bound.apply_transitivity(b_bound)
            if (isinstance(self, IntervalOO)
                    or isinstance(self, IntervalCO)
                    or InSet(_b, RealNeg).readily_provable()):
                # member in R^{<0}
                return InSet(_n, RealNeg).prove()
            else:
                # member in R^{≤0}
                return InSet(_n, RealNonPos).prove()


class IntervalOOMembership(RealIntervalMembership):
    def __init__(self, element, domain):
        RealIntervalMembership.__init__(self, element, domain)
    
    @prover
    def derive_left_relaxed_membership(self, **defaults_config):
        '''
        From x in (a, b), derive x in [a, b).
        '''
        return self.domain.deduce_left_relaxed_membership(self.element)

    @prover
    def derive_right_relaxed_membership(self, **defaults_config):
        '''
        From x in (a, b), derive x in (a, b].
        '''
        return self.domain.deduce_right_relaxed_membership(self.element)

    @prover
    def derive_fully_relaxed_membership(self, **defaults_config):
        '''
        From x in (a, b), derive x in [a, b].
        '''
        return self.domain.deduce_fully_relaxed_membership(self.element)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Prove that membership in a real interval is a Boolean
        (true or false).
        '''
        from . import interval_oo_membership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_oo_membership_is_bool.instantiate(
                {a: _a, b: _b, x: _x}, auto_simplify=False)


class IntervalOCMembership(RealIntervalMembership):
    def __init__(self, element, domain):
        RealIntervalMembership.__init__(self, element, domain)

    @prover
    def derive_relaxed_membership(self, **defaults_config):
        '''
        From x in (a, b], derive x in [a, b].
        '''
        return self.domain.deduce_relaxed_membership(self.element)

    @prover
    def derive_left_relaxed_membership(self, **defaults_config):
        '''
        From x in (a, b], derive x in [a, b].
        '''
        return self.derive_relaxed_membership()

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Prove that membership in a real interval is a Boolean
        (true or false).
        '''
        from . import interval_oc_membership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_oc_membership_is_bool.instantiate(
                {a: _a, b: _b, x: _x}, auto_simplify=False)


class IntervalCOMembership(RealIntervalMembership):
    def __init__(self, element, domain):
        RealIntervalMembership.__init__(self, element, domain)
    
    @prover
    def derive_relaxed_membership(self, **defaults_config):
        '''
        From x in [a, b), derive x in [a, b].
        '''
        return self.domain.deduce_relaxed_membership(self.element)

    @prover
    def derive_right_relaxed_membership(self, **defaults_config):
        '''
        From x in [a, b), derive x in [a, b].
        '''
        return self.derive_relaxed_membership()

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Prove that membership in a real interval is a Boolean
        (true or false).
        '''
        from . import interval_co_membership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_co_membership_is_bool.instantiate(
                {a: _a, b: _b, x: _x}, auto_simplify=False)


class IntervalCCMembership(RealIntervalMembership):
    def __init__(self, element, domain):
        RealIntervalMembership.__init__(self, element, domain)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Prove that membership in a real interval is a Boolean
        (true or false).
        '''
        from . import interval_cc_membership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_cc_membership_is_bool.instantiate(
                {a: _a, b: _b, x: _x}, auto_simplify=False)


class RealIntervalNonmembership(SetNonmembership):
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
        SetNonmembership.__init__(self, element, domain)
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
        if ((InSet(_a, Real)).readily_provable() and
           (InSet(_b, Real)).readily_provable() and
           (InSet(_x, Real)).readily_provable()):
            yield self.deduce_real_element_bounds

    def _readily_provable(self):
        '''
        The Nonmembership is readily provabile if the element
        is readily known to be non-Real or its readily known to be 
        below/above the lower/upper bound.
        '''
        _x = self.element
        lb, ub = self.domain.member_bounds(_x)
        return InSet(_x, Real).readily_disprovable() or (
                lb.readily_disprovable() or ub.readily_disprovable())

    @prover
    def conclude(self, **defaults_config):
        '''
        From x not in Real, or a real x such that x < a, x <= a,
        x > b, or x >= b, derive and return
        [element x not in IntervalXX(a, b)],
        where self is the IntervalNonmembership object and XX is
        OO, CO, OC, and/or CC as appropriate.
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element

        # if x not real, then x cannot be in a real interval
        if NotInSet(_x, Real).readily_provable():

            # 4 cases corresponding to the 4 types of real intervals

            if isinstance(self.domain, IntervalOO):
                from . import not_real_not_in_interval_oo
                return not_real_not_in_interval_oo.instantiate(
                        {a: _a, b: _b, x: _x})

            if isinstance(self.domain, IntervalCO):
                from . import not_real_not_in_interval_co
                return not_real_not_in_interval_co.instantiate(
                        {a: _a, b: _b, x: _x})

            if isinstance(self.domain, IntervalOC):
                from . import not_real_not_in_interval_oc
                return not_real_not_in_interval_oc.instantiate(
                        {a: _a, b: _b, x: _x})

            if isinstance(self.domain, IntervalCC):
                from . import not_real_not_in_interval_cc
                return not_real_not_in_interval_cc.instantiate(
                        {a: _a, b: _b, x: _x})

        if isinstance(self.domain, IntervalOO):
            from . import real_not_in_interval_oo
            return real_not_in_interval_oo.instantiate(
                    {a: _a, b: _b, x: _x})

        if isinstance(self.domain, IntervalCO):
            from . import real_not_in_interval_co
            return real_not_in_interval_co.instantiate(
                    {a: _a, b: _b, x: _x})

        if isinstance(self.domain, IntervalOC):
            from . import real_not_in_interval_oc
            return real_not_in_interval_oc.instantiate(
                    {a: _a, b: _b, x: _x})

        if isinstance(self.domain, IntervalCC):
            from . import real_not_in_interval_cc
            return real_not_in_interval_cc.instantiate(
                    {a: _a, b: _b, x: _x})

        # from . import not_int_not_in_interval
        # try:
        #     return not_int_not_in_interval.instantiate(
        #             {a: _a, b: _b, x: _x}, assumptions=assumptions)
        # except ProofFailure:
        #     from . import int_not_in_interval
        #     return int_not_in_interval.instantiate(
        #             {a: _a, b: _b, x: _x}, assumptions=assumptions)

    # @prover
    # def deduce_int_element_bounds(self, **defaults_config):
    #     from . import bounds_for_int_not_in_interval
    #     _a = self.domain.lower_bound
    #     _b = self.domain.upper_bound
    #     _x = self.element
    #     return bounds_for_int_not_in_interval.instantiate(
    #         {a: _a, b: _b, x: _x}, assumptions=assumptions)

    @prover
    def deduce_real_element_bounds(self, **defaults_config):
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
                    {a: _a, b: _b, x: _x})

        if isinstance(self.domain, IntervalCO):
            from . import bounds_for_real_not_in_interval_co
            return bounds_for_real_not_in_interval_co.instantiate(
                    {a: _a, b: _b, x: _x})

        if isinstance(self.domain, IntervalOC):
            from . import bounds_for_real_not_in_interval_oc
            return bounds_for_real_not_in_interval_oc.instantiate(
                    {a: _a, b: _b, x: _x})

        if isinstance(self.domain, IntervalCC):
            from . import bounds_for_real_not_in_interval_cc
            return bounds_for_real_not_in_interval_cc.instantiate(
                    {a: _a, b: _b, x: _x})

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
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
                    {a: _a, b: _b, x: _x}, auto_simplify=False)

        if isinstance(self.domain, IntervalCO):
            from . import interval_co_nonmembership_is_bool
            return interval_co_nonmembership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, auto_simplify=False)

        if isinstance(self.domain, IntervalOC):
            from . import interval_oc_nonmembership_is_bool
            return interval_oc_nonmembership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, auto_simplify=False)

        if isinstance(self.domain, IntervalCC):
            from . import interval_cc_nonmembership_is_bool
            return interval_cc_nonmembership_is_bool.instantiate(
                    {a: _a, b: _b, x: _x}, auto_simplify=False)
