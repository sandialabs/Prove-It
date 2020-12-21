from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit._common_ import q
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
        yield lambda assumptions: self.deduce_member_in_real(member, assumptions)

    def membership_object(self, element):
        return RationalMembership(element, self)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import rational_membership_is_bool
        from proveit._common_ import x
        return rational_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_real(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.number_sets.real_numbers._theorems_ import rational_within_real
        return rational_within_real.derive_superset_membership(
            member, assumptions)


class RationalNonZeroSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNonZero', r'\mathbb{Q}^{\neq 0}',
                           theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_rational(member,
                                                                 assumptions)

    def membership_object(self, element):
        return RationalMembership(element, self)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import rational_non_zero_membership_is_bool
        from proveit._common_ import x
        return rational_non_zero_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import rational_non_zero_in_rational
        return rational_non_zero_in_rational.derive_superset_membership(
            member, assumptions)


class RationalPosSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalPos', r'\mathbb{Q}^+',
                           theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_rational(member,
                                                                 assumptions)

    def membership_object(self, element):
        return RationalMembership(element, self)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import rational_pos_membership_is_bool
        from proveit._common_ import x
        return rational_pos_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_pos_within_rational.derive_superset_membership(
            member, assumptions)


class RationalNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNeg', r'\mathbb{Q}^-',
                           theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_rational(member,
                                                                 assumptions)

    def membership_object(self, element):
        return RationalMembership(element, self)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import rational_neg_membership_is_bool
        from proveit._common_ import x
        return rational_neg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_neg_within_rational.derive_superset_membership(
            member, assumptions)


class RationalNonNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'RationalNonNeg', r'\mathbb{Q}^{\geq 0}',
                           theory=__file__)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalNonNeg'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_rational(member,
                                                                 assumptions)

    def membership_object(self, element):
        return RationalMembership(element, self)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import rational_non_neg_membership_is_bool
        from proveit._common_ import x
        return rational_non_neg_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_rational(self, member, assumptions=USE_DEFAULTS):
        return rational_non_neg_within_rational.derive_superset_membership(
            member, assumptions)


class RationalMembership(NumberMembership):
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    def conclude(self, assumptions):
        from proveit.logic import InSet, NotEquals
        from proveit.numbers import (
            Rational, RationalNonZero, RationalPos, RationalNeg,
            RationalNonNeg, Less, Greater, GreaterEq, zero)

        # If we known the element is in Q, we may be able to
        # prove that is in RationalNonZero, RationalPos, RationalNeg, or
        # RationalNonNeg if we know its relation to zero.
        if (self.number_set != Rational and
                InSet(self.element, Rational).proven(assumptions)):
            if self.number_set == RationalNonZero:
                if NotEquals(self.element, zero).proven(assumptions):
                    from ._theorems_ import non_zero_rational_is_rational_non_zero
                    return non_zero_rational_is_rational_non_zero.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalPos:
                if Greater(self.element, zero).proven(assumptions):
                    from ._theorems_ import positive_rational_is_rational_pos
                    return positive_rational_is_rational_pos.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalNeg:
                if Less(self.element, zero).proven():
                    from ._theorems_ import negative_rational_is_rational_neg
                    return negative_rational_is_rational_neg.instantiate(
                        {q: self.element}, assumptions=assumptions)
            if self.number_set == RationalNonNeg:
                if GreaterEq(self.element, zero).proven():
                    from ._theorems_ import non_neg_rational_in_rational_neg
                    return non_neg_rational_in_rational_neg.instantiate(
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
        from ._theorems_ import reduced_nat_pos_ratio

        if self.number_set == RationalPos:
            return reduced_nat_pos_ratio.instantiate(
                {q: self.element}, assumptions=assumptions).choose(
                numerator_var, denominator_var)
        else:
            raise NotImplementedError(
                "choose_reduced_rational_fraction() implemented only "
                "for the RationalPos NumberSet (but the {0} NumberSet "
                "was provided instead).".format(self.number_set))


try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for
    # the first time, but fine after that.
    from ._theorems_ import (nat_within_rational, nat_within_rational_non_neg,
                             nat_pos_in_rational_pos,
                             nat_pos_in_rational_non_zero,
                             rational_non_zero_in_rational,
                             rational_pos_within_rational,
                             rational_neg_within_rational,
                             rational_non_neg_within_rational,
                             rational_pos_in_rational_non_zero,
                             rational_neg_in_rational_non_zero,
                             rational_pos_within_rational_non_neg,
                             zero_is_rational)
except BaseException:
    pass
