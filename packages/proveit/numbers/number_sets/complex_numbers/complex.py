import proveit
from proveit import prover, relation_prover
from proveit import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet


class ComplexSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Complex', r'\mathbb{C}', 
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .complex_membership import ComplexMembership    
        return ComplexMembership(element)

    @staticmethod
    @prover
    def left_mult_both_sides_of_equals(relation, multiplier,
                                       **defaults_config):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.numbers.multiplication import left_mult_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_mult_eq.instantiate(
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
        from proveit.numbers.multiplication import left_mult_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_mult_neq.instantiate(
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
        from proveit.numbers.multiplication import right_mult_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        
        from proveit import defaults
        return right_mult_eq.instantiate(
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
        from proveit.numbers.multiplication import right_mult_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_mult_neq.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def divide_both_sides_of_equals(relation, divisor,
                                    **defaults_config):
        '''
        Divide both sides of the Equals relation by the 'divisor'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.division import div_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")

        from proveit import defaults
        return div_eq.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def divide_both_sides_of_notequals(relation, divisor, 
                                       **defaults_config):
        '''
        Divide both sides of the NotEquals relation by the 'divisor'.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.division import div_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return div_neq.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_add_both_sides_of_equals(relation, addend,
                                      **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.numbers.addition import left_add_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_add_eq.instantiate(
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
        from proveit.numbers.addition import left_add_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_add_neq.instantiate(
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
        from proveit.numbers.addition import right_add_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_add_eq.instantiate(
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
        from proveit.numbers.addition import right_add_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_add_neq.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def exponentiate_both_sides_of_equals(relation, exponent,
                                          **defaults_config):
        '''
        Add both sides of the Equals relation by the 'exponent'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.exponentiation import exp_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return exp_eq.instantiate(
            {a: exponent, x: relation.lhs, y: relation.rhs})

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

    @staticmethod
    @prover
    def square_both_sides_of_equals(relation, **defaults_config):
        '''
        Square both sides of the Equals relation.
        '''
        from proveit.numbers import two
        return ComplexSet.exponentiate_both_sides_of_equals(
            relation, two)

    @staticmethod
    @prover
    def square_both_sides_of_notequals(relation, **defaults_config):
        '''
        Square both sides of the NotEquals relation.
        '''
        from proveit.numbers import two
        return ComplexSet.exponentiate_both_sides_of_notequals(
            relation, two)

    @staticmethod
    @prover
    def square_root_both_sides_of_equals(relation, **defaults_config):
        '''
        Take the square root of both sides of the Equals relation.
        '''
        from proveit.numbers import frac, one, two, Exp
        new_rel = ComplexSet.exponentiate_both_sides_of_equals(
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
        new_rel = ComplexSet.exponentiate_both_sides_of_notequals(
            relation, frac(one, two))
        new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel

    @staticmethod
    @prover
    def abs_both_sides_of_equals(relation, **defaults_config):
        '''
        Apply absolute value (Abs) to both sides of an Equals relation
        specified by 'relation', returning the equality of the absolute
        values. The original equality relation 'relation' must either
        be a known judgment, proveable, or assumed. For example:
            Complex.abs_both_sides_of_equals(
            Equals(a, b),
            assumptions=[InSet(a, Complex), InSet(a, Complex),
                         Equals(a, b)])
        will return: assumptions |- |a| = |b|.
        '''
        from proveit.logic import Equals
        from proveit.numbers.absolute_value import abs_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return abs_eq.instantiate(
            {x: relation.lhs, y: relation.rhs})

    # @staticmethod
    # @prover
    # def abs_both_sides_of_notequals(relation, =**defaults_config):
    #     '''
    #     UNDER CONSTRUCTION
    #     '''
    #     from proveit.logic import NotEquals
    #     from proveit.numbers.exponentiation import exp_neq
    #     if not isinstance(relation, NotEquals):
    #         TypeError("'relation' expected to be NotEquals")
    #     return exp_neq.instantiate(
    #         {a: exponent, x: relation.lhs, y: relation.rhs})

class ComplexNonZeroSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'ComplexNonZero', r'\mathbb{C}^{\neq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .complex_membership import ComplexNonZeroMembership    
        return ComplexNonZeroMembership(element)
    

# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from . import real_within_complex, real_pos_within_complex, real_neg_within_complex, int_within_complex, nat_within_complex

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first
    # time, but fine after that.
    from . import real_within_complex, int_within_complex, nat_within_complex
