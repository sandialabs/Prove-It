from proveit import (x, defaults, Literal, ProofFailure, prover,
                     UnsatisfiedPrerequisites, safe_dummy_var)
from proveit.logic import (Equals, InSet, SetMembership, SubsetEq,
                           ProperSubset)


class NumberSet(Literal):
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

    def includes(self, other_set):
        '''
        Return True if this NumberSet includes the 'other_set' set.
        '''
        from proveit.numbers.number_operation import (
            sorted_number_sets, standard_number_sets, deduce_number_set)
        if other_set is None: return False
        if other_set == self: return True
        if SubsetEq(other_set, self).proven():
            return True

        if other_set not in standard_number_sets:    
            # For example, 'other_set' could be an integer Interval
            # or real IntervalCC, IntervalOC, ...), so let's see if
            # we can prove that an arbitrary variable in the other_set
            # is also in self.

            # No worry about conflicts with assumptions because the 
            # variable will be bound by a quantifier:
            _x = safe_dummy_var(self, other_set,
                                avoid_default_assumption_conflicts=False)
            assumptions = defaults.assumptions + (InSet(_x, other_set),)
            #deduce_number_set(_x, assumptions=assumptions)
            if InSet(_x, self).readily_provable(assumptions=assumptions):
                #if not SubsetEq(other_set, self).proven():
                #    SubsetEq(other_set, self).conclude_as_folded()
                return True

        # Try one level of indirection via SubsetEq.
        for number_set in sorted_number_sets:
            if number_set in (other_set, self):
                continue
            if (SubsetEq(other_set, number_set).proven() and
                    SubsetEq(number_set, self).proven()):
                return True

        return False # Not known to include the 'other'

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
        Raise UnsatisfiedPrerequisites if they are not standard number
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
        raise UnsatisfiedPrerequisites()

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
        Return True iff we can readily prove this number set membership;
        specifically, return True if the most restrictive readily
        provable standard number set of the element is included by the
        number set of this membership.
        '''
        from proveit.numbers import readily_provable_number_set
        try:
            provable_number_set = readily_provable_number_set(self.element)
        except UnsatisfiedPrerequisites:
            return False
        return self.number_set.includes(provable_number_set)

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to deduce that the given element is in the number set under
        the given assumptions.
        '''
        from proveit.numbers import (readily_provable_number_set,
                                     deduce_number_set)

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

        provable_number_set = readily_provable_number_set(element)
        if number_set.includes(provable_number_set) and (
                InSet(element, provable_number_set).proven()):
            # We already know the element is in a number set that
            # includes the desired one.
            return (SubsetEq(provable_number_set, number_set)
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
        else:
            if hasattr(self, 'conclude_as_last_resort'):
                return self.conclude_as_last_resort()
            msg = str(element) + " has no 'deduce_in_number_set' method."
            raise ProofFailure(InSet(self.element, self.number_set),
                               defaults.assumptions, msg)
