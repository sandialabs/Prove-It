from proveit import (x, defaults, Literal, ProofFailure, prover,
                     UnsatisfiedPrerequisites, safe_dummy_var)
from proveit.logic import (Equals, InSet, SetMembership, SubsetEq,
                           ProperSubset)


class NumberSet(Literal):
    # Map pairs of standard number sets to True/False depending on
    # whether the first includes the latter.  Used to speed up
    # NumberSet.includes.
    _standard_number_set_inclusion_truths = dict()
    
    def __init__(self, string, latex, *, theory, styles, fence_when_forced=False):
        Literal.__init__(self, string, latex, theory=theory, styles=styles,
                         fence_when_forced=fence_when_forced)

    def membership_object(self, element):
        return NumberMembership(element, self)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects for when the given member is in this number
        set.  The default is to have no side-effects, but this
        can be adapted for the various NumberSet classes.
        '''
        return
        yield

    @property
    def plus_operator(self):
        '''
        Add._operator_ is the default plus operation for number sets
        (e.g., as groups or fields).
        '''
        from proveit.numbers import Add
        return Add._operator_

    @property
    def times_operator(self):
        '''
        Mult._operator_ is the default times operation for number sets
        (e.g., as fields or rings).
        '''
        from proveit.numbers import Mult
        return Mult._operator_

    def is_infinite_set(self):
        '''
        Return True if this is an infinite number set.
        '''
        from proveit.numbers.number_operation import standard_number_sets
        if self in standard_number_sets:
            return True
        raise NotImplementedError(
                "%s not known as an ininite set"%self)

    def readily_includes(self, other_set):
        '''
        Return True if this NumberSet is expected to include 
        the 'other_set' set (without a proof).
        '''
        from proveit.numbers import (
                Integer, Real, 
                NaturalPos, Natural, IntegerNeg, IntegerNonPos,
                RealPos, RealNonNeg, RealNeg, RealNonPos,
                readily_provable_number_set,
                Interval, IntervalCC, IntervalOC, IntervalCO, IntervalOO)
        from proveit.numbers.number_operation import (
            sorted_number_sets, standard_number_sets)
        if other_set is None: return False
        if other_set == self: return True
        if SubsetEq(other_set, self).proven():
            return True # already known

        if self in standard_number_sets and other_set in standard_number_sets:
            inclusion_truths = NumberSet._standard_number_set_inclusion_truths
            if (self, other_set) in inclusion_truths:
                return inclusion_truths[(self, other_set)]
            does_include = False
            # Try one level of indirection via SubsetEq.
            for number_set in sorted_number_sets:
                if number_set in (other_set, self):
                    continue
                if (SubsetEq(other_set, number_set).proven() and
                        SubsetEq(number_set, self).proven()):
                    does_include = True
                    break
            # remember for future reference
            inclusion_truths[(self, other_set)] = does_include
            return does_include
        elif self in standard_number_sets:
            if isinstance(other_set, Interval):
                # The other set is an integer interval.
                if self.readily_includes(Integer):
                    # Integer includes this integer interval.
                    return True
                lower_ns = readily_provable_number_set(other_set.lower_bound)
                if NaturalPos.readily_includes(lower_ns):
                    # NaturalPos includes this integer interval.
                    return self.readily_includes(NaturalPos)
                if Natural.readily_includes(lower_ns):
                    # Natural includes this integer interval.
                    return self.readily_includes(Natural)
                upper_ns = readily_provable_number_set(other_set.upper_bound)
                if IntegerNeg.readily_includes(upper_ns):
                    # IntegerNeg includes this integer interval.
                    return self.readily_includes(IntegerNeg)
                if IntegerNonPos.readily_includes(upper_ns):
                    # IntegerNonPos includes this integer interval.
                    return self.readily_includes(IntegerNonPos)
            elif isinstance(other_set, IntervalCC) or (
                    isinstance(other_set, IntervalOC) or
                    isinstance(other_set, IntervalCO) or
                    isinstance(other_set, IntervalOO)):
                # The other set is an real interval.
                if self.readily_includes(Real):
                    # Real includes this integer interval.
                    return True
                lower_ns = readily_provable_number_set(other_set.lower_bound)
                if RealPos.readily_includes(lower_ns):
                    # RealPos includes this integer interval.
                    return self.readily_includes(RealPos)
                if RealNonNeg.readily_includes(lower_ns):
                    if isinstance(other_set, IntervalOC) or (
                            isinstance(other_set, IntervalOO)):
                        # RealPos includes this integer interval.
                        return self.readily_includes(RealPos)
                    # RealNonNeg includes this integer interval.
                    return self.readily_includes(RealNonNeg)
                upper_ns = readily_provable_number_set(other_set.upper_bound)
                if RealNeg.readily_includes(upper_ns):
                    # RealNeg includes this integer interval.
                    return self.readily_includes(RealNeg)                
                if RealNonPos.readily_includes(upper_ns):
                    if isinstance(other_set, IntervalCO) or (
                            isinstance(other_set, IntervalOO)):
                        # RealNeg includes this integer interval.
                        return self.readily_includes(RealNeg)
                    # IntegerNonPos includes this integer interval.
                    return self.readily_includes(RealNonPos)
                
        # As a last resort, check if membership in the other set 
        # guarantees membership in the other purely by automation.

        # No worry about conflicts with assumptions because the 
        # variable will be bound by a quantifier:
        _x = safe_dummy_var(self, other_set,
                            avoid_default_assumption_conflicts=False)
        assumptions = defaults.assumptions + (InSet(_x, other_set),)
        #deduce_number_set(_x, assumptions=assumptions)
        return InSet(_x, self).proven(assumptions=assumptions)

    def deduce_superset_eq_relation(self, superset):
        '''
        Prove that a standard is a superset another standard number set.
        Raise UnsatisfiedPrerequisites if they are not standard number
        sets that have the correct relationship.
        '''
        from proveit.numbers.number_operation import sorted_number_sets
        if SubsetEq(self, superset).proven():
            return SubsetEq(self, superset).prove()
        # Try one level of indirection via SubsetEq.
        for number_set in sorted_number_sets:
            if number_set in (self, superset):
                continue
            if (SubsetEq(self, number_set).proven() and
                    SubsetEq(number_set, superset).proven()):
                return SubsetEq(self, number_set).apply_transitivity(
                        SubsetEq(number_set, superset))
        raise UnsatisfiedPrerequisites(
                "%s subset %s not immediately known"%(self, superset))

    def deduce_proper_superset_relation(self, superset):
        '''
        Prove that a standard is a proper superset another standard 
        number set.
        Raise ProofFailure if they are not standard number
        sets that have the correct relationship.
        '''
        from proveit.numbers.number_operation import sorted_number_sets
        if ProperSubset(self, superset).proven():
            return ProperSubset(self, superset).prove()
        # Try one level of indirection via SubsetEq.
        for number_set in sorted_number_sets:
            if number_set in (self, superset):
                continue
            if (ProperSubset(self, number_set).proven() and
                    ProperSubset(number_set, superset).proven()):
                return ProperSubset(self, number_set).apply_transitivity(
                        ProperSubset(number_set, superset))
        raise UnsatisfiedPrerequisites(
                "%s subset %s not immediately known"%(self, superset))

class NumberMembership(SetMembership):
    def __init__(self, element, number_set):
        SetMembership.__init__(self, element, number_set)
        self.number_set = number_set

    def side_effects(self, judgment):
        '''
        Yield side-effects for when the represented membership,
        that self.element is in self.number_set, is proven.
        '''
        number_set, element = self.number_set, self.element
        if not isinstance(judgment.expr, InSet):
            raise ValueError(
                "Expecting the judgment of a NumberMembership "
                "side_effects call to be for an InSet expression.")
        if judgment.element != element:
            raise ValueError("NumberMembership.side_effects called with a "
                             "judgment that is inconsistent w.r.t. the "
                             "element.")
        if judgment.domain != number_set:
            raise ValueError("NumberMembership.side_effects called with a "
                             "judgment that is inconsistent w.r.t. the "
                             "domain.")
        for side_effect in number_set.membership_side_effects(judgment):
            yield side_effect

    def readily_in_bool(self):
        '''
        Number membership is always a boolean.
        '''
        return True

    def _readily_provable(self):
        '''
        Return True iff we can readily prove this number set membership
        directly (not through known/provable equalities which is handled
        at the InSet.conclude level);
        specifically, return True if the most restrictive direct, 
        readily provable standard number set of the element is included
        by the number set of this membership.
        '''
        from proveit.numbers import readily_provable_number_set
        provable_number_set = readily_provable_number_set(
                self.element, must_be_direct=True)
        if provable_number_set is None: return False
        return self.number_set.readily_includes(provable_number_set)

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to deduce that the given element is in the number set under
        the given assumptions.
        '''
        from proveit.logic import is_irreducible_value
        from proveit.numbers import readily_provable_number_set

        element = self.element
        number_set = self.number_set

        '''
        # Maybe let's not simplify first.  If
        # See if we can simplify the element first.
        if hasattr(element, 'simplification'):
            simplification = element.simplification(assumptions=assumptions)
            element = simplification.rhs
            if element != self.element:
                # Prove membersip for the simplified element
                elem_in_set = InSet(element, self.number_set).prove(assumptions)
                # Substitute into the original.
                return simplification.sub_left_side_into(elem_in_set, assumptions)
        '''

        proven_number_set = readily_provable_number_set(
                element, automation=False)
        if number_set.readily_includes(proven_number_set):
            # We already know the element is in a number set that
            # includes the desired one.
            return (SubsetEq(proven_number_set, number_set)
                    .derive_superset_membership(element))

        # Try the 'deduce_in_number_set' method.
        if hasattr(element, 'deduce_in_number_set'):
            # Try to deduce membership directly in the desired number
            # set via 'deduce_in_number_set'.
            try:
                return element.deduce_in_number_set(self.number_set)
            except (NotImplementedError, UnsatisfiedPrerequisites) as e:
                if hasattr(self, 'conclude_as_last_resort'):
                    return self.conclude_as_last_resort()
                raise ProofFailure(InSet(self.element, self.number_set),
                                   defaults.assumptions, str(e))
        elif not is_irreducible_value(element):
            # Try a known evaluation.
            try:
                evaluation = Equals.get_known_evaluation(element)
            except UnsatisfiedPrerequisites:
                evaluation = None
            if evaluation is not None:
                membership = InSet(evaluation.rhs, self.domain)
                membership = membership.prove()
                return membership.inner_expr().element.substitute(
                        element)
        if hasattr(self, 'conclude_as_last_resort'):
            return self.conclude_as_last_resort()
        msg = str(element) + " has no 'deduce_in_number_set' method."
        raise ProofFailure(InSet(self.element, self.number_set),
                           defaults.assumptions, msg)
