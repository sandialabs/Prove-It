from proveit import defaults, prover
from proveit import a, x
from proveit.logic import NotEquals, InSet
from proveit.numbers.number_sets.real_numbers import (
        Real, RealPos, RealNeg, RealNonNeg, RealNonPos, RealNonZero)
from proveit.numbers.number_sets.number_set import NumberMembership


class RealMembership(NumberMembership):
    '''
    Defines methods that apply to membership in real numbers
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, Real)
    
    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Real' for a given n.
        '''
        yield self.derive_element_in_complex

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import real_membership_is_bool
        return real_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_complex(self, **defaults_config):
        from proveit.numbers.number_sets.complex_numbers import (
                real_within_complex)
        return real_within_complex.derive_superset_membership(
            self.element, auto_simplify=False)


class RealNonZeroMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNonZero
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNonZero)

    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import zero
        if (InSet(self.element, Real).proven() and
                NotEquals(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in RealNonZero by proving it is real
        and not zero.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import nonzero_real_is_real_nonzero
        return nonzero_real_is_real_nonzero.instantiate(
            {a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonZero' 
        for a given n.
        '''
        yield self.derive_element_in_real
        yield self.derive_element_not_zero
        yield self.derive_element_in_complex_nonzero

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import real_nonzero_membership_is_bool
        from proveit import x
        return real_nonzero_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_not_zero(self, **defaults_config):
        from . import nonzero_if_in_real_nonzero
        return nonzero_if_in_real_nonzero.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from . import real_nonzero_within_real
        return real_nonzero_within_real.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_complex_nonzero(self, **defaults_config):
        from proveit.numbers.number_sets.complex_numbers import (
                real_nonzero_within_complex_nonzero)
        return real_nonzero_within_complex_nonzero.derive_superset_membership(
            self.element, auto_simplify=False)


class RealPosMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealPos
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealPos)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import zero, greater
        if (InSet(self.element, Real).proven() and
                greater(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in Real by proving it is real and positive.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import pos_real_is_real_pos
        return pos_real_is_real_pos.instantiate(
            {a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealPos' for a given n.
        '''
        yield self.derive_element_in_real
        yield self.derive_element_in_real_nonzero
        yield self.derive_element_in_real_nonneg
        yield self.derive_element_lower_bound

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import real_pos_membership_is_bool
        from proveit import x
        return real_pos_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        from . import positive_if_in_real_pos
        return positive_if_in_real_pos.instantiate(
            {x: self.element}, auto_simplify=False)
    
    @prover
    def derive_element_in_real(self, **defaults_config):
        from . import real_pos_within_real
        return real_pos_within_real.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_nonzero(self, **defaults_config):
        from . import real_pos_within_real_nonzero
        thm = real_pos_within_real_nonzero
        return thm.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_nonneg(self, **defaults_config):
        from . import real_pos_within_real_nonneg
        thm = real_pos_within_real_nonneg
        return thm.derive_superset_membership(
                self.element, auto_simplify=False)


class RealNegMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNeg
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNeg)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import zero, Less
        if (InSet(self.element, Real).proven() and
                Less(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in Real by proving it is real and negative.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import neg_real_is_real_neg
        return neg_real_is_real_neg.instantiate(
            {a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNeg' for a given n.
        '''
        yield self.derive_element_in_real
        yield self.derive_element_in_real_nonzero
        yield self.derive_element_in_real_nonpos
        yield self.derive_element_upper_bound

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import real_neg_membership_is_bool
        from proveit import x
        return real_neg_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        from . import negative_if_in_real_neg
        return negative_if_in_real_neg.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from . import real_neg_within_real
        return real_neg_within_real.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_nonzero(self, **defaults_config):
        from . import real_neg_within_real_nonzero
        thm = real_neg_within_real_nonzero
        return thm.derive_superset_membership(self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_nonpos(self, **defaults_config):
        from . import real_neg_within_real_nonpos
        thm = real_neg_within_real_nonpos
        return thm.derive_superset_membership(self.element, auto_simplify=False)


class RealNonNegMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNonNeg
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNonNeg)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import zero, greater_eq
        if (InSet(self.element, Real).proven() and
                greater_eq(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in Real by proving it is real and non-negative.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import nonneg_real_is_real_nonneg
        return nonneg_real_is_real_nonneg.instantiate(
            {a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonNeg' for a given n.
        '''
        yield self.derive_element_in_real
        yield self.derive_element_lower_bound

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import real_nonneg_membership_is_bool
        from proveit import x
        return real_nonneg_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        from . import nonneg_if_in_real_nonneg
        return nonneg_if_in_real_nonneg.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from . import real_nonneg_within_real
        return real_nonneg_within_real.derive_superset_membership(
            self.element, auto_simplify=False)


class RealNonPosMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RealNonPos
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, RealNonPos)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import zero, LessEq
        if (InSet(self.element, Real).proven() and
                LessEq(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in Real by proving it is real and non-positive.
        This is called in NumberMembership.conclude as a last resort.
        '''
        from . import nonpos_real_is_real_nonpos
        return nonpos_real_is_real_nonpos.instantiate(
            {a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in RealNonPos' for a given n.
        '''
        yield self.derive_element_in_real
        yield self.derive_element_upper_bound

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import real_nonpos_membership_is_bool
        return real_nonpos_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        from . import nonpos_if_in_real_nonpos
        return nonpos_if_in_real_nonpos.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from . import real_nonpos_within_real
        return real_nonpos_within_real.derive_superset_membership(
            self.element, auto_simplify=False)
