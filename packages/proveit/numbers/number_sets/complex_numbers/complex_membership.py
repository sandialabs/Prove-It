from proveit import prover, relation_prover
from proveit import x
from proveit.numbers.number_sets.complex_numbers import (
        Complex, ComplexNonZero)
from proveit.numbers.number_sets.number_set import NumberMembership


class ComplexMembership(NumberMembership):

    '''
    Defines methods that apply to membership in complex numbers.
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, Complex)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import complex_membership_is_bool
        from proveit import x
        return complex_membership_is_bool.instantiate(
                {x: self.element}, auto_simplify=False)


class ComplexNonZeroMembership(NumberMembership):

    '''
    Defines methods that apply to membership in non-zero complex
    numbers.
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, ComplexNonZero)

    @prover
    def conclude(self, **defaults_config):
        from proveit.logic import NotEquals, InSet
        from proveit.numbers import zero
        if (InSet(self.element, Complex).proven() and
                NotEquals(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in ComplexNonZero by proving it is complex
        and non-zero.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import nonzero_complex_is_complex_nonzero
        return nonzero_complex_is_complex_nonzero.instantiate(
            {x:self.element})


    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'x in Complex' for a given x.
        '''
        yield self.derive_element_in_complex
        yield self.derive_element_not_zero

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import complex_nonzero_membership_is_bool
        from proveit import x
        return complex_nonzero_membership_is_bool.instantiate(
                {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_not_zero(self, **defaults_config):
        from . import nonzero_if_in_complex_nonzero
        return nonzero_if_in_complex_nonzero.instantiate(
                {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_complex(self, **defaults_config):
        from . import complex_nonzero_within_complex
        return complex_nonzero_within_complex.derive_superset_membership(
            self.element, auto_simplify=False)
