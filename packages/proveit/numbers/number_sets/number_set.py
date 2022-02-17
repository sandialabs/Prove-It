from proveit import (Literal, ProofFailure, UnsatisfiedPrerequisites,
                     defaults, prover)
from proveit.logic import Equals, InSet, SetMembership, SubsetEq


class NumberSet(Literal):
    def __init__(self, string, latex, *, theory, styles, fence_when_forced=False):
        Literal.__init__(self, string, latex, theory=theory, styles=styles,
                         fence_when_forced=fence_when_forced)

    def includes(self, other_set):
        '''
        Return True of this NumberSet includes the 'other'
        set.
        '''
        return SubsetEq(other_set, self).proven()

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

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to deduce that the given element is in the number set under
        the given assumptions.
        '''
        from proveit.numbers import deduce_number_set

        element = self.element

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
        try:
            deduce_number_set(element)
        except (ProofFailure, UnsatisfiedPrerequisites):
            pass
        membership = InSet(element, self.number_set)
        if membership.proven():
            return membership.prove()

        # Try the 'deduce_in_number_set' method.
        if hasattr(element, 'deduce_in_number_set'):
            try:
                return element.deduce_in_number_set(self.number_set)
            except NotImplementedError as e:
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
