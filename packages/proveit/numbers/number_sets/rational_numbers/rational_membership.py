from proveit import prover
from proveit import q
from proveit.logic import NotEquals, InSet
from proveit.numbers.number_sets.number_set import NumberMembership

class RationalMembership(NumberMembership):
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in Rational' for a given q.
        '''
        yield self.derive_element_in_real

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import rational_membership_is_bool
        from proveit import x
        return rational_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import rational_within_real
        return rational_within_real.derive_superset_membership(
            self.element, auto_simplify=False)

    # This is not a @prover because it does not return a Judgment.
    def choose_rational_fraction(self, numerator_var, denominator_var,
                                **defaults_config):
        '''
        Choose Skolem "constants" (really variables with proper a
        ssumptions) for
            x = a/b, either "a in Z" or "a in N", b in N
        where x is the element in the rationals set, a and b are the
        Skolem "constants".
        For the RationalPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        Returns an ExprTuple of assumptions added to 
        defaults.assumptions.
        '''
        pass

    # This is not a @prover because it does not return a Judgment.
    def choose_reduced_rational_fraction(self, numerator_var, denominator_var,
                                         **defaults_config):
        '''
        Choose Skolem "constants" (Rationally variables with proper a
        ssumptions) for
            x = a/b, either "a in Z" or "a in N", b in N, gcd(a, b) = 1
        where x is the element in the rationals set, a and b are the
        Skolem "constants".
        For the RationalPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        Returns an ExprTuple of assumptions added to 
        defaults.assumptions.
        '''
        from . import reduced_nat_pos_ratio
        from proveit.numbers import RationalPos

        if self.number_set == RationalPos:
            return reduced_nat_pos_ratio.instantiate(
                {q: self.element}, **defaults_config).choose(
                numerator_var, denominator_var)
        else:
            raise NotImplementedError(
                "choose_reduced_rational_fraction() implemented only "
                "for the RationalPos NumberSet (but the {0} NumberSet "
                "was provided instead).".format(self.number_set))


class RationalNonZeroMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNonZero
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNonZero
        RationalMembership.__init__(self, element, RationalNonZero)

    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import Rational, zero
        if (InSet(self.element, Rational).proven() and
                NotEquals(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in RationalNonZero by proving it is rational
        and not zero.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import nonzero_rational_is_rational_nonzero
        return nonzero_rational_is_rational_nonzero.instantiate(
            {q:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonZero'
        for a given q.
        '''
        yield self.derive_element_notzero
        yield self.derive_element_in_rational
        yield self.derive_element_in_real_nonzero

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import rational_nonzero_membership_is_bool
        from proveit import x
        return rational_nonzero_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_notzero(self, **defaults_config):
        from . import nonzero_if_in_rational_nonzero
        return nonzero_if_in_rational_nonzero.instantiate(
            {q: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from . import rational_nonzero_within_rational
        return rational_nonzero_within_rational.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_nonzero(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonzero_within_real_nonzero)
        return rational_nonzero_within_real_nonzero.derive_superset_membership(
            self.element, auto_simplify=False)

class RationalPosMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalPos
    '''

    def __init__(self, element):
        from proveit.numbers import RationalPos
        RationalMembership.__init__(self, element, RationalPos)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import Rational, greater, zero
        if (InSet(self.element, Rational).proven() and
                greater(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in RationalPos by proving it is rational
        and positive.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import pos_rational_is_rational_pos
        return pos_rational_is_rational_pos.instantiate({q:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        yield self.derive_element_lower_bound
        yield self.derive_element_in_rational
        yield self.derive_element_in_rational_nonzero
        yield self.derive_element_in_rational_nonneg
        yield self.derive_element_in_real_pos

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import rational_pos_membership_is_bool
        from proveit import x
        return rational_pos_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        from . import positive_if_in_rational_pos
        return positive_if_in_rational_pos.instantiate(
            {q: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from . import rational_pos_within_rational
        return rational_pos_within_rational.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_nonzero(self, **defaults_config):
        from . import rational_pos_within_rational_nonzero
        thm = rational_pos_within_rational_nonzero
        return thm.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_nonneg(self, **defaults_config):
        from . import rational_pos_within_rational_nonneg
        thm = rational_pos_within_rational_nonneg
        return thm.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_pos(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import (
                rational_pos_within_real_pos)
        return rational_pos_within_real_pos.derive_superset_membership(
            self.element, auto_simplify=False)

        
class RationalNegMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNeg
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNeg
        RationalMembership.__init__(self, element, RationalNeg)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import Rational, Less, zero
        if (InSet(self.element, Rational).proven() and
                Less(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in RationalNeg by proving it is rational
        and negative.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import neg_rational_is_rational_neg
        return neg_rational_is_rational_neg.instantiate({q:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNeg'
        for a given q.
        '''
        yield self.derive_element_upper_bound
        yield self.derive_element_in_rational
        yield self.derive_element_in_rational_nonzero
        yield self.derive_element_in_rational_nonpos
        yield self.derive_element_in_rational_nonpos
        yield self.derive_element_in_real_neg

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import rational_neg_membership_is_bool
        from proveit import x
        return rational_neg_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        from . import negative_if_in_rational_neg
        return negative_if_in_rational_neg.instantiate(
            {q: self.element}, auto_simplify=False)    

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from . import rational_neg_within_rational
        return rational_neg_within_rational.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_nonzero(self, **defaults_config):
        from . import rational_neg_within_rational_nonzero
        thm = rational_neg_within_rational_nonzero
        return thm.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_nonpos(self, **defaults_config):
        from . import rational_neg_within_rational_nonpos
        thm = rational_neg_within_rational_nonpos
        return thm.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_neg(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import (
                rational_neg_within_real_neg)
        return rational_neg_within_real_neg.derive_superset_membership(
            self.element, auto_simplify=False)


class RationalNonNegMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNonNeg
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNonNeg
        RationalMembership.__init__(self, element, RationalNonNeg)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import Rational, greater_eq, zero
        if (InSet(self.element, Rational).proven() and
                greater_eq(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in RationalNeg by proving it is rational
        and non-negative.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import nonneg_rational_is_rational_nonneg
        return nonneg_rational_is_rational_nonneg.instantiate(
            {q:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonNeg'
        for a given q.
        '''
        yield self.derive_element_lower_bound
        yield self.derive_element_in_rational
        yield self.derive_element_in_real_nonneg

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import rational_nonneg_membership_is_bool
        from proveit import x
        return rational_nonneg_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        from . import nonneg_if_in_rational_nonneg
        return nonneg_if_in_rational_nonneg.instantiate(
            {q: self.element}, auto_simplify=False)  

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from . import rational_nonneg_within_rational
        return rational_nonneg_within_rational.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_nonneg(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonneg_within_real_nonneg)
        return rational_nonneg_within_real_nonneg.derive_superset_membership(
            self.element, auto_simplify=False)


class RationalNonPosMembership(RationalMembership):

    '''
    Defines methods that apply to membership in RationalNonPos
    '''

    def __init__(self, element):
        from proveit.numbers import RationalNonPos
        RationalMembership.__init__(self, element, RationalNonPos)
    
    @prover
    def conclude(self, **defaults_config):
        from proveit.numbers import Rational, LessEq, zero
        if (InSet(self.element, Rational).proven() and
                LessEq(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in RationalNeg by proving it is rational
        and non-positive.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import nonpos_rational_is_rational_nonpos
        return nonpos_rational_is_rational_nonpos.instantiate(
            {q:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonPos'
        for a given q.
        '''
        yield self.derive_element_upper_bound
        yield self.derive_element_in_rational
        yield self.derive_element_in_real_nonpos

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import rational_nonpos_membership_is_bool
        from proveit import x
        return rational_nonpos_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        from . import nonpos_if_in_rational_nonpos
        return nonpos_if_in_rational_nonpos.instantiate(
            {q: self.element}, auto_simplify=False)  

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from . import rational_nonpos_within_rational
        return rational_nonpos_within_rational.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_real_nonpos(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonpos_within_real_nonpos)
        return rational_nonpos_within_real_nonpos.derive_superset_membership(
            self.element, auto_simplify=False)
