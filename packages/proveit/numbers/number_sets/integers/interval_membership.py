from proveit import defaults, prover, ProofFailure
from proveit import a, b, n, x
from proveit.logic import InSet, SetNonmembership
from proveit.numbers import Less, LessEq, greater, greater_eq 
from proveit.numbers import (zero, Integer, IntegerNeg, IntegerNonPos,
                             Natural, NaturalPos)
from proveit.numbers.number_sets.number_set import NumberMembership

class IntervalMembership(NumberMembership):

    '''
    Defines methods that apply to membership in an Interval,
    InSet(x, Interval(m, n), where Interval(m, n) represents a set
    of contiguous integers of the form {m, m+1, m+2, ..., n}.
    '''

    def __init__(self, element, domain):
        NumberMembership.__init__(self, element, domain)
        self.domain = domain

    @prover
    def conclude(self, **defaults_config):
        '''
        From [element in Integer] and [lower_bound <= element] and
        [element <= upper_bound], derive and return
        [element in Interval(lower_bound, upper_bound)]
        '''
        element = self.element
        if hasattr(element, 'deduce_in_number_set'):
            try:
                return element.deduce_in_number_set(self.domain)
            except (NotImplementedError, ProofFailure):
                # If that didn't work, try 'deduce_elem_in_set'.
                pass
        return self.domain.deduce_elem_in_set(element)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving n in an Interval for a given n.
        '''
        from proveit.logic import InSet
        from proveit.numbers import Natural, IntegerNonPos
        yield self.derive_element_lower_bound
        yield self.derive_element_upper_bound
        yield self.derive_element_in_integer
        # Derive that the element is in a restriced number set if
        # we can.
        yield self.derive_element_in_restricted_number_set_if_known
        # Added but commented the following out while we debate the
        # wisdom of further side-effects
        # yield lambda: self.deduce_member_in_real(member)

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import interval_membership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_membership_is_bool.instantiate(
            {a: _a, b: _b, x: _x})

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        from . import interval_lower_bound
        return interval_lower_bound.instantiate(
            {a: self.domain.lower_bound, b: self.domain.upper_bound, 
             n:self.element},
            auto_simplify=False)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        from . import interval_upper_bound
        return interval_upper_bound.instantiate(
            {a: self.domain.lower_bound, b: self.domain.upper_bound, 
             n: self.element},
            auto_simplify=False)

    @prover
    def derive_element_in_integer(self, **defaults_config):
        from . import int_interval_within_int
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        return int_interval_within_int.instantiate(
                {a:_a, b:_b}).derive_superset_membership(
                        self.element, auto_simplify=False)

    @prover
    def derive_element_in_natural(self, **defaults_config):
        InSet(self.domain.lower_bound, Natural).prove()
        return self.derive_element_in_restricted_number_set()

    @prover
    def derive_element_in_natural_pos(self, **defaults_config):
        InSet(self.domain.lower_bound, NaturalPos).prove()
        return self.derive_element_in_restricted_number_set()

    @prover
    def derive_element_in_integer_neg(self, **defaults_config):
        InSet(self.domain.upper_bound, IntegerNeg).prove()
        return self.derive_element_in_restricted_number_set()

    @prover
    def derive_element_in_integer_nonpos(self, **defaults_config):
        InSet(self.domain.upper_bound, IntegerNonPos).prove()
        return self.derive_element_in_restricted_number_set()

    @prover
    def derive_element_in_restricted_number_set_if_known(
            self, **defaults_config):
        from proveit import UnsatisfiedPrerequisites
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        if (InSet(_a, Natural).proven() or 
                InSet(_b, IntegerNonPos).proven()):
            return self.derive_element_in_restricted_number_set()
        # Without employing further automation, can we prove the
        # lower bound is non-negative or the upper bound is
        # non-positive?
        try:
            _a.deduce_in_number_set(Natural, automation=False)
        except Exception:
            pass
        try:
            _b.deduce_in_number_set(IntegerNonPos, automation=False)
        except Exception:
            pass
        if (InSet(_a, Natural).proven() or 
                InSet(_b, IntegerNonPos).proven()):
            return self.derive_element_in_restricted_number_set()
        raise UnsatisfiedPrerequisites(
                "Must know that the lower bound is non-negative or the "
                "upper bound is non-positive to perform "
                "derive_element_in_restricted_number_set_if_known")

    @prover
    def derive_element_in_restricted_number_set(
            self, **defaults_config):
        '''
        From (member in Interval(x, y)), where x ≥ 0 or y ≤ 0,
        deduce that the element is in Natural, NaturalPos, IntegerNeg,
        or IntegerNonPos as appropriate.
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _n = self.element

        # We wish to deduce a fact based upon the following
        # membership fact:
        self.expr.prove()

        if (not InSet(_a, Natural).proven() and 
                not InSet(_b, IntegerNonPos).proven()):
            # If we don't know that a ≥ 0 or b ≤ 0, we can't prove
            # the element is in either restricted number set
            # (NaturalPos or IntegerNeg).  So, try to sort a, b, 0
            # to work this out.
            LessEq.sort([_a, _b, zero])

        if InSet(_a, Natural).proven():
            try:
                _a.deduce_in_number_set(NaturalPos, automation=False)         
            except Exception:
                pass
            if InSet(_a, NaturalPos).proven():
                # member in N^{>0}
                lower_bounding = self.derive_element_lower_bound()
                a_bounding = greater(_a, zero)
                lower_bounding.apply_transitivity(a_bounding)
                return InSet(_n, NaturalPos).prove()
            else:
                # member in N
                lower_bounding = self.derive_element_lower_bound()
                a_bounding = greater_eq(_a, zero)
                lower_bounding.apply_transitivity(a_bounding)
                return InSet(_n, Natural).prove()
        if InSet(_b, IntegerNonPos).proven():
            try:
                _b.deduce_in_number_set(IntegerNeg, automation=False)        
            except Exception:
                pass
            if InSet(_b, IntegerNeg).proven():
                # member in Z^{<0}
                upper_bounding = self.derive_element_upper_bound()
                b_bounding = Less(_b, zero)
                upper_bounding.apply_transitivity(b_bounding)
                return InSet(_n, IntegerNeg).prove()
            else:
                # member in Z^{≤0}
                upper_bounding = self.derive_element_upper_bound()
                b_bounding = LessEq(_b, zero)
                upper_bounding.apply_transitivity(b_bounding)
                return InSet(_n, IntegerNonPos).prove()
    

class IntervalNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in an Interval(m, n)
    where Interval(m, n) represents a set of contiguous integers.
    of the form {m, m+1, m+2, ..., n}.
    UNDER CONSTRUCTION
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Yield some possible side effects of Interval set nonmembership:
        (1) if element is an integer, deduce some possible bounds on it;
        '''
        if InSet(self.element, Integer).proven():
            yield self.deduce_int_element_bounds

    @prover
    def conclude(self, **defaults_config):
        '''
        From x not in Integers, or an integer x such that x < a or x > b,
        derive and return [element x not in Interval(a, b)],
        where self is the IntervalNonmembership object.
        '''
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        if InSet(self.element, Integer).proven():
            from . import int_not_in_interval
            return int_not_in_interval.instantiate(
                    {a: _a, b: _b, x: _x})
        else:
            from . import not_int_not_in_interval
            return not_int_not_in_interval.instantiate(
                    {a: _a, b: _b, x: _x})

    @prover
    def deduce_int_element_bounds(self, **defaults_config):
        from . import bounds_for_int_not_in_interval
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return bounds_for_int_not_in_interval.instantiate(
            {a: _a, b: _b, x: _x})

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import interval_nonmembership_is_bool
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _x = self.element
        return interval_nonmembership_is_bool.instantiate(
            {a: _a, b: _b, x: _x})
