import proveit
from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit import q
from proveit.logic import Membership
from proveit.numbers.number_sets.number_set import NumberSet, NumberMembership


class RationalSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'Rational', r'\mathbb{Q}',
                           theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in Rational' for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_real(
                member, assumptions)

    def membership_object(self, element):
        return RationalMembership(element, self)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_membership_is_bool
        from proveit import x
        return rational_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import rational_within_real
        return rational_within_real.derive_superset_membership(
            member, assumptions)


class RationalNonZeroSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNonZero', r'\mathbb{Q}^{\neq 0}',
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_notzero(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_real_nonzero(
                member, assumptions)

    def deduce_member_notzero(self, member, assumptions=USE_DEFAULTS):
        from . import nonzero_if_in_rational_nonzero
        return nonzero_if_in_rational_nonzero.instantiate(
            {q: member}, assumptions=assumptions)

    def membership_object(self, element):
        return RationalMembership(element, self)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonzero_membership_is_bool
        from proveit import x
        return rational_nonzero_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_nonzero_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_real_nonzero(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonzero_within_real_nonzero)
        return rational_nonzero_within_real_nonzero.derive_superset_membership(
            member, assumptions)


class RationalPosSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalPos', r'\mathbb{Q}^+',
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_lower_bound(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_nonzero(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_nonneg(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_real_pos(
                member, assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from . import positive_if_in_rational_pos
        return positive_if_in_rational_pos.instantiate(
            {q: member}, assumptions=assumptions)        

    def membership_object(self, element):
        return RationalMembership(element, self)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_pos_membership_is_bool
        from proveit import x
        return rational_pos_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_pos_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_rational_nonzero(self, member, 
                                          assumptions=USE_DEFAULTS):
        thm = rational_pos_within_rational_nonzero
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_rational_nonneg(self, member, 
                                         assumptions=USE_DEFAULTS):
        thm = rational_pos_within_rational_nonneg
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_real_pos(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_pos_within_real_pos)
        return rational_pos_within_real_pos.derive_superset_membership(
            member, assumptions)


class RationalNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNeg', r'\mathbb{Q}^-',
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_upper_bound(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_nonzero(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_nonpos(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational_nonpos(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_real_neg(
                member, assumptions)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from . import negative_if_in_rational_neg
        return negative_if_in_rational_neg.instantiate(
            {q: member}, assumptions=assumptions)    

    def membership_object(self, element):
        return RationalMembership(element, self)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_neg_membership_is_bool
        from proveit import x
        return rational_neg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_neg_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_rational_nonzero(self, member, 
                                          assumptions=USE_DEFAULTS):
        thm = rational_neg_within_rational_nonzero
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_rational_nonpos(self, member, 
                                         assumptions=USE_DEFAULTS):
        thm = rational_neg_within_rational_nonpos
        return thm.derive_superset_membership(member, assumptions)

    def deduce_member_in_real_neg(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_neg_within_real_neg)
        return rational_neg_within_real_neg.derive_superset_membership(
            member, assumptions)


class RationalNonNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNonNeg', r'\mathbb{Q}^{\geq 0}',
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_lower_bound(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_real_nonneg(
                member, assumptions)

    def deduce_member_lower_bound(self, member, assumptions=USE_DEFAULTS):
        from . import nonneg_if_in_rational_nonneg
        return nonneg_if_in_rational_nonneg.instantiate(
            {q: member}, assumptions=assumptions)  

    def membership_object(self, element):
        return RationalMembership(element, self)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonneg_membership_is_bool
        from proveit import x
        return rational_nonneg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_nonneg_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_real_nonneg(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonneg_within_real_nonneg)
        return rational_nonneg_within_real_nonneg.derive_superset_membership(
            member, assumptions)


class RationalNonPosSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNonPos', r'\mathbb{Q}^{\leq 0}',
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_upper_bound(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_rational(
                member, assumptions)
        yield lambda assumptions: self.deduce_member_in_real_nonpos(
                member, assumptions)

    def deduce_member_upper_bound(self, member, assumptions=USE_DEFAULTS):
        from . import nonpos_if_in_rational_nonpos
        return nonpos_if_in_rational_nonpos.instantiate(
            {q: member}, assumptions=assumptions)  

    def membership_object(self, element):
        return RationalMembership(element, self)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import rational_nonpos_membership_is_bool
        from proveit import x
        return rational_nonpos_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_nonpos_within_rational.derive_superset_membership(
            member, assumptions)

    def deduce_member_in_real_nonpos(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers import (
                rational_nonpos_within_real_nonpos)
        return rational_nonpos_within_real_nonpos.derive_superset_membership(
            member, assumptions)


class RationalMembership(NumberMembership):
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    def conclude(self, assumptions):
        from proveit.logic import InSet, NotEquals
        from proveit.numbers import (
            Rational, RationalNonZero, RationalPos, RationalNeg,
            RationalNonNeg, Less, greater, greater_eq, zero)

        # If we known the element is in Q, we may be able to
        # prove that is in RationalNonZero, RationalPos, RationalNeg, or
        # RationalNonNeg if we know its relation to zero.
        if (self.number_set != Rational and
                InSet(self.element, Rational).proven(assumptions)):
            if self.number_set == RationalNonZero:
                if NotEquals(self.element, zero).proven(assumptions):
                    from . import nonzero_rational_is_rational_nonzero
                    return nonzero_rational_is_rational_nonzero.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalPos:
                if greater(self.element, zero).proven(assumptions):
                    from . import positive_rational_is_rational_pos
                    return positive_rational_is_rational_pos.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalNeg:
                if Less(self.element, zero).proven():
                    from . import negative_rational_is_rational_neg
                    return negative_rational_is_rational_neg.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalNonNeg:
                if greater_eq(self.element, zero).proven():
                    from . import nonneg_rational_in_rational_neg
                    return nonneg_rational_in_rational_neg.instantiate(
                        {q: self.element}, assumptions=assumptions)

        # Resort to the default NumberMembership.conclude strategies.
        return NumberMembership.conclude(self, assumptions)

    def choose_rational_fraction(self, numerator_var, denominator_var,
                                 *, assumptions=USE_DEFAULTS):
        '''
        Choose Skolem "constants" (really variables with proper a
        ssumptions) for
            x = a/b, either "a in Z" or "a in N", b in N
        where x is the element in the rationals set, a and b are the
        Skolem "constants".
        For the RationalPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        '''
        pass

    def choose_reduced_rational_fraction(self, numerator_var, denominator_var,
                                         *, assumptions=USE_DEFAULTS):
        '''
        Choose Skolem "constants" (really variables with proper a
        ssumptions) for
            x = a/b, either "a in Z" or "a in N", b in N, gcd(a, b) = 1
        where x is the element in the rationals set, a and b are the
        Skolem "constants".
        For the RationalPos set, use "a in N"; otherwise, use "a in Z".
        Call "eliminate" to finish the Skolemization proof.
        '''
        from proveit.numbers import RationalPos
        from . import reduced_nat_pos_ratio

        if self.number_set == RationalPos:
            return reduced_nat_pos_ratio.instantiate(
                {q: self.element}, assumptions=assumptions).choose(
                numerator_var, denominator_var)
        else:
            raise NotImplementedError(
                "choose_reduced_rational_fraction() implemented only "
                "for the RationalPos NumberSet (but the {0} NumberSet "
                "was provided instead).".format(self.number_set))


if proveit.defaults.automation:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for
    # the first time, but fine after that.
    from . import (nat_within_rational, 
                   int_within_rational,
                   nonzero_int_within_rational_nonzero,
                   nat_within_rational_nonneg,
                   nat_pos_within_rational_pos,
                   neg_int_within_rational_neg,
                   nonpos_int_within_rational_nonpos,
                   rational_nonzero_within_rational,
                   rational_pos_within_rational,
                   rational_neg_within_rational,
                   rational_nonneg_within_rational,
                   rational_nonpos_within_rational,
                   rational_pos_within_rational_nonzero,
                   rational_neg_within_rational_nonzero,
                   rational_pos_within_rational_nonneg,
                   rational_neg_within_rational_nonpos,
                   zero_is_rational)
