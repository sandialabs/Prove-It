from proveit import prover
import proveit
from proveit.logic import Equals, NotEquals
from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet


class RealSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Real', r'\mathbb{R}',
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .real_membership import RealMembership    
        return RealMembership(element)

    @staticmethod
    @prover
    def left_add_both_sides_of_equals(relation, addend,
                                      **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the left.
        '''
        from proveit.numbers.addition import left_add_eq_real
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_add_eq_real.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_add_both_sides_of_notequals(relation, addend,
                                         **defaults_config):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the left.
        '''
        from proveit.numbers.addition import left_add_neq_real
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_add_neq_real.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_add_both_sides_of_equals(relation, addend,
                                       **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the right.
        '''
        from proveit.numbers.addition import right_add_eq_real
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_add_eq_real.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_add_both_sides_of_notequals(relation, addend,
                                          **defaults_config):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the right.
        '''
        from proveit.numbers.addition import right_add_neq_real
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_add_neq_real.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_mult_both_sides_of_equals(relation, multiplier,
                                       **defaults_config):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers.multiplication import left_mult_eq_real
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_mult_eq_real.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_mult_both_sides_of_notequals(relation, multiplier,
                                          **defaults_config):
        '''
        Multiply both sides of a NonEquals relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers.multiplication import left_mult_neq_real
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_mult_neq_real.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_mult_both_sides_of_equals(relation, multiplier,
                                        **defaults_config):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers.multiplication import right_mult_eq_real
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_mult_eq_real.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_mult_both_sides_of_notequals(relation, multiplier,
                                           **defaults_config):
        '''
        Multiply both sides of a NotEquals relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers.multiplication import right_mult_neq_real
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_mult_neq_real.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})


    @staticmethod
    @prover
    def divide_both_sides_of_equals(relation, divisor,
                                    **defaults_config):
        '''
        Divide both sides of the Equals relation by the 'divisor'.
        '''
        from proveit.numbers.division import div_eq_real
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return div_eq_real.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def divide_both_sides_of_notequals(relation, divisor, 
                                       **defaults_config):
        '''
        Divide both sides of the NotEquals relation by the 'divisor'.
        '''
        from proveit.numbers.division import div_neq_real
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return div_neq_real.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def exponentiate_both_sides_of_equals(relation, exponent,
                                          **defaults_config):
        '''
        Add both sides of the Equals relation by the 'exponent'.
        '''
        from proveit.numbers.exponentiation import exp_eq_real
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return exp_eq_real.instantiate(
            {a: exponent, x: relation.lhs, y: relation.rhs})

    """
    @staticmethod
    @prover
    def exponentiate_both_sides_of_notequals(relation, exponent,
                                             **defaults_config):
        '''
        Add both sides of the NotEquals relation by the 'exponent'.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.exponentiation import exp_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return exp_neq.instantiate(
            {a: exponent, x: relation.lhs, y: relation.rhs})
    """

    @staticmethod
    @prover
    def square_both_sides_of_equals(relation, **defaults_config):
        '''
        Square both sides of the Equals relation.
        '''
        from proveit.numbers import two
        return RealSet.exponentiate_both_sides_of_equals(
            relation, two)

    @staticmethod
    @prover
    def square_both_sides_of_notequals(relation, **defaults_config):
        '''
        Square both sides of the NotEquals relation.
        '''
        from proveit.numbers import two
        return RealSet.exponentiate_both_sides_of_notequals(
            relation, two)

    @staticmethod
    @prover
    def square_root_both_sides_of_equals(relation, **defaults_config):
        '''
        Take the square root of both sides of the Equals relation.
        '''
        from proveit.numbers import frac, one, two, Exp
        new_rel = RealSet.exponentiate_both_sides_of_equals(
            relation, frac(one, two))
        if isinstance(new_rel.lhs, Exp) and new_rel.lhs.exponent==frac(one, two):
            new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        if isinstance(new_rel.rhs, Exp) and new_rel.lhs.exponent==frac(one, two):
            new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel

    @staticmethod
    @prover
    def square_root_both_sides_of_notequals(relation, **defaults_config):
        '''
        Take the square root of both sides of the NotEquals relation.
        '''
        from proveit.numbers import frac, one, two
        new_rel = RealSet.exponentiate_both_sides_of_notequals(
            relation, frac(one, two))
        new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel


class RealNonZeroSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonZero', r'\mathbb{R}^{\neq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonZeroMembership    
        return RealNonZeroMembership(element)


class RealPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealPos', r'\mathbb{R}^+', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealPosMembership    
        return RealPosMembership(element)


class RealNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNeg', r'\mathbb{R}^-', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNegMembership    
        return RealNegMembership(element)


class RealNonNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonNeg', r'\mathbb{R}^{\ge 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonNegMembership    
        return RealNonNegMembership(element)


class RealNonPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonPos', r'\mathbb{R}^{\le 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonPosMembership    
        return RealNonPosMembership(element)


if proveit.defaults.sideeffect_automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from . import (
        zero_set_within_real, zero_set_within_real_nonneg, 
        zero_set_within_real_nonpos,
        int_within_real,
        nat_within_real,
        nat_pos_within_real,
        nat_pos_within_real_pos,
        nat_within_real_nonneg,
        nat_pos_within_real_nonneg,
        nonzero_int_within_real_nonzero,
        neg_int_within_real_neg,
        nonpos_int_within_real_nonpos,
        rational_within_real,
        rational_nonzero_within_real_nonzero,
        rational_pos_within_real_pos,
        rational_neg_within_real_neg,
        rational_nonneg_within_real_nonneg,
        rational_nonpos_within_real_nonpos,
        real_pos_within_real,
        real_pos_within_real_nonzero,
        real_pos_within_real_nonneg,
        real_neg_within_real,
        real_neg_within_real_nonzero,
        real_neg_within_real_nonpos,
        real_nonneg_within_real,
        real_nonpos_within_real)
