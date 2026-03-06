import proveit
from proveit import prover
from proveit import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet


class IntegerSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Integer', r'\mathbb{Z}', 
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .integer_membership import IntegerMembership    
        return IntegerMembership(element)

    @staticmethod
    @prover
    def left_add_both_sides_of_equals(relation, addend,
                                      **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.numbers.addition import left_add_eq_int
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_add_eq_int.instantiate(
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
        from proveit.numbers.addition import left_add_neq_int
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_add_neq_int.instantiate(
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
        from proveit.numbers.addition import right_add_eq_int
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_add_eq_int.instantiate(
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
        from proveit.numbers.addition import right_add_neq_int
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_add_neq_int.instantiate(
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
        from proveit.numbers.multiplication import left_mult_eq_int
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_mult_eq_int.instantiate(
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
        from proveit.numbers.multiplication import left_mult_neq_int
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_mult_neq_int.instantiate(
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
        from proveit.numbers.multiplication import right_mult_eq_int
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_mult_eq_int.instantiate(
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
        from proveit.numbers.multiplication import right_mult_neq_int
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_mult_neq_int.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})


    @staticmethod
    @prover
    def divide_both_sides_of_equals(relation, divisor,
                                    **defaults_config):
        '''
        Divide both sides of the Equals relation by the 'divisor'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.division import div_eq_int
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return div_eq_int.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def divide_both_sides_of_notequals(relation, divisor, 
                                       **defaults_config):
        '''
        Divide both sides of the NotEquals relation by the 'divisor'.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.division import div_neq_int
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return div_neq_int.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def exponentiate_both_sides_of_equals(relation, exponent,
                                          **defaults_config):
        '''
        Add both sides of the Equals relation by the 'exponent'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.exponentiation import exp_eq_int
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return exp_eq_int.instantiate(
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
        return IntegerSet.exponentiate_both_sides_of_equals(
            relation, two)

    @staticmethod
    @prover
    def square_both_sides_of_notequals(relation, **defaults_config):
        '''
        Square both sides of the NotEquals relation.
        '''
        from proveit.numbers import two
        return IntegerSet.exponentiate_both_sides_of_notequals(
            relation, two)

    @staticmethod
    @prover
    def square_root_both_sides_of_equals(relation, **defaults_config):
        '''
        Take the square root of both sides of the Equals relation.
        '''
        from proveit.numbers import frac, one, two, Exp
        new_rel = IntegerSet.exponentiate_both_sides_of_equals(
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
        new_rel = IntegerSet.exponentiate_both_sides_of_notequals(
            relation, frac(one, two))
        new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel


class IntegerNonZeroSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerNonZero', r'\mathbb{Z}^{\neq 0}', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerNonZeroMembership    
        return IntegerNonZeroMembership(element)


class IntegerNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerNeg', r'\mathbb{Z}^{-}', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerNegMembership    
        return IntegerNegMembership(element)


class IntegerNonPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerNonPos', r'\mathbb{Z}^{\leq 0}', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerNonPosMembership    
        return IntegerNonPosMembership(element)

class IntegerEvenSet(NumberSet):
    '''
    Class to represent the even integers {..., -2, 0, 2, 4, ...}
    and provide related methods. The even integer set appears as
    'IntegerEven' in string output and as mathbb 'E' in LaTeX output.
    '''
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerEven', r'\mathbb{E}',
                           theory=__file__, styles=styles,
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerEvenMembership    
        return IntegerEvenMembership(element)

class IntegerOddSet(NumberSet):
    '''
    Class to represent the odd integers {..., -3, -1, 1, 3, ...}
    and provide related methods. The odd integer set appears as
    'IntegerOdd' in string output and as mathbb 'O' in LaTeX output.
    '''
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'IntegerOdd', r'\mathbb{O}',
                           theory=__file__, styles=styles,
                           fence_when_forced=True)

    def membership_object(self, element):
        from .integer_membership import IntegerOddMembership    
        return IntegerOddMembership(element)


class PrimeSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'PRIMES', r'\mathbb{P}', 
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .integer_membership import PrimeMembership    
        return PrimeMembership(element)


if proveit.defaults.running_theory_notebook is None:
    # Import some fundamental theorems without quantifiers when not 
    # running an common/axioms/theorems theory notebook.
    from . import (zero_set_within_int, zero_set_within_nonpos_int,
                   prime_within_int,
                   nat_within_int,
                   nat_pos_within_int,
                   nat_pos_within_nonzero_int,
                   nonzero_int_within_int,
                   neg_int_within_int, neg_int_within_nonzero_int,
                   neg_int_within_nonpos_int,
                   nonpos_int_within_int)
