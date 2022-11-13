import proveit
from proveit import prover, maybe_fenced_string
from proveit import a, x, y, q
from proveit.numbers.number_sets.number_set import NumberSet, NumberMembership


class RationalSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Rational', r'\mathbb{Q}',
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .rational_membership import RationalMembership    
        return RationalMembership(element, self)

    @staticmethod
    @prover
    def left_add_both_sides_of_equals(relation, addend,
                                      **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.numbers.addition import left_add_eq_rational
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_add_eq_rational.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_add_both_sides_of_notequals(relation, addend,
                                         **defaults_config):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.addition import left_add_neq_rational
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_add_neq_rational.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_add_both_sides_of_equals(relation, addend,
                                       **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the right.
        '''
        from proveit.logic import Equals
        from proveit.numbers.addition import right_add_eq_rational
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_add_eq_rational.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_add_both_sides_of_notequals(relation, addend,
                                          **defaults_config):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the right.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.addition import right_add_neq_rational
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_add_neq_rational.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_mult_both_sides_of_equals(relation, multiplier,
                                       **defaults_config):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.numbers.multiplication import left_mult_eq_rational
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_mult_eq_rational.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_mult_both_sides_of_notequals(relation, multiplier,
                                          **defaults_config):
        '''
        Multiply both sides of a NonEquals relation by the 'multiplier'
        on the left.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.multiplication import left_mult_neq_rational
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_mult_neq_rational.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_mult_both_sides_of_equals(relation, multiplier,
                                        **defaults_config):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the right.
        '''
        from proveit.logic import Equals
        from proveit.numbers.multiplication import right_mult_eq_rational
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_mult_eq_rational.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_mult_both_sides_of_notequals(relation, multiplier,
                                           **defaults_config):
        '''
        Multiply both sides of a NotEquals relation by the 'multiplier'
        on the right.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.multiplication import right_mult_neq_rational
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_mult_neq_rational.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})


    @staticmethod
    @prover
    def divide_both_sides_of_equals(relation, divisor,
                                    **defaults_config):
        '''
        Divide both sides of the Equals relation by the 'divisor'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.division import div_eq_rational
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return div_eq_rational.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def divide_both_sides_of_notequals(relation, divisor, 
                                       **defaults_config):
        '''
        Divide both sides of the NotEquals relation by the 'divisor'.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.division import div_neq_rational
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return div_neq_rational.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def exponentiate_both_sides_of_equals(relation, exponent,
                                          **defaults_config):
        '''
        Add both sides of the Equals relation by the 'exponent'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.exponentiation import exp_eq_rational
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return exp_eq_rational.instantiate(
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
        return RationalSet.exponentiate_both_sides_of_equals(
            relation, two)

    @staticmethod
    @prover
    def square_both_sides_of_notequals(relation, **defaults_config):
        '''
        Square both sides of the NotEquals relation.
        '''
        from proveit.numbers import two
        return RationalSet.exponentiate_both_sides_of_notequals(
            relation, two)

    @staticmethod
    @prover
    def square_root_both_sides_of_equals(relation, **defaults_config):
        '''
        Take the square root of both sides of the Equals relation.
        '''
        from proveit.numbers import frac, one, two, Exp
        new_rel = RationalSet.exponentiate_both_sides_of_equals(
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
        new_rel = RationalSet.exponentiate_both_sides_of_notequals(
            relation, frac(one, two))
        new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel


class RationalNonZeroSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonZero', r'\mathbb{Q}^{\neq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonZeroMembership    
        return RationalNonZeroMembership(element)


class RationalPosSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalPos', r'\mathbb{Q}^+',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalPosMembership    
        return RationalPosMembership(element)


class RationalNegSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNeg', r'\mathbb{Q}^-',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNegMembership    
        return RationalNegMembership(element)


class RationalNonNegSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonNeg', r'\mathbb{Q}^{\geq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonNegMembership    
        return RationalNonNegMembership(element)


class RationalNonPosSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonPos', r'\mathbb{Q}^{\leq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonPosMembership    
        return RationalNonPosMembership(element)


if proveit.defaults.running_theory_notebook is None:
    # Import some fundamental theorems without quantifiers when not 
    # running an common/axioms/theorems theory notebook.
    from . import (            
            zero_set_within_rational, zero_set_within_rational_nonneg,
            zero_set_within_rational_nonpos,           
            nat_within_rational, 
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
            rational_neg_within_rational_nonpos)
