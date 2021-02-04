import proveit
from proveit import USE_DEFAULTS
from proveit import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet


class ComplexSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Complex', r'\mathbb{C}', theory=__file__)

    def deduce_in_set_is_bool(self, element, assumptions=USE_DEFAULTS):
        from .theorems import in_complex_is_bool
        return in_complex_is_bool.instantiate({a: element}, assumptions)

    def deduce_not_in_set_is_bool(self, element, assumptions=USE_DEFAULTS):
        from .theorems import not_in_complex_is_bool
        return not_in_complex_is_bool.instantiate({a: element}, assumptions)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import complex_membership_is_bool
        from proveit import x
        return complex_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    @staticmethod
    def left_mult_both_sides_of_equals(relation, multiplier,
                                       assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.numbers.multiplication import left_mult_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_mult_eq.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def left_mult_both_sides_of_notequals(relation, multiplier,
                                          assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of a NonEquals relation by the 'multiplier'
        on the left.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.multiplication import left_mult_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_mult_neq.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def right_mult_both_sides_of_equals(relation, multiplier,
                                        assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the right.
        '''
        from proveit.logic import Equals
        from proveit.numbers.multiplication import right_mult_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_mult_eq.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def right_mult_both_sides_of_notequals(relation, multiplier,
                                           assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of a NotEquals relation by the 'multiplier'
        on the right.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.multiplication import right_mult_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_mult_neq.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def divide_both_sides_of_equals(relation, divisor,
                                    assumptions=USE_DEFAULTS):
        '''
        Divide both sides of the Equals relation by the 'divisor'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.division import div_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return div_eq.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def divide_both_sides_of_notequals(relation, divisor,
                                       assumptions=USE_DEFAULTS):
        '''
        Divide both sides of the NotEquals relation by the 'divisor'.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.division import div_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return div_neq.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def left_add_both_sides_of_equals(relation, addend,
                                      assumptions=USE_DEFAULTS):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import Equals
        from proveit.numbers.addition import left_add_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_add_eq.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def left_add_both_sides_of_notequals(relation, addend,
                                         assumptions=USE_DEFAULTS):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the left.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.addition import left_add_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_add_neq.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def right_add_both_sides_of_equals(relation, addend,
                                       assumptions=USE_DEFAULTS):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the right.
        '''
        from proveit.logic import Equals
        from proveit.numbers.addition import right_add_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_add_eq.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def right_add_both_sides_of_notequals(relation, addend,
                                          assumptions=USE_DEFAULTS):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the right.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.addition import right_add_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_add_neq.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def exponentiate_both_sides_of_equals(relation, exponent,
                                          assumptions=USE_DEFAULTS):
        '''
        Add both sides of the Equals relation by the 'exponent'.
        '''
        from proveit.logic import Equals
        from proveit.numbers.exponentiation import exp_eq
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return exp_eq.instantiate(
            {a: exponent, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def exponentiate_both_sides_of_notequals(relation, exponent,
                                             assumptions=USE_DEFAULTS):
        '''
        Add both sides of the NotEquals relation by the 'exponent'.
        '''
        from proveit.logic import NotEquals
        from proveit.numbers.exponentiation import exp_neq
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return exp_neq.instantiate(
            {a: exponent, x: relation.lhs, y: relation.rhs},
            assumptions=assumptions)

    @staticmethod
    def square_both_sides_of_equals(relation,
                                    assumptions=USE_DEFAULTS):
        '''
        Square both sides of the Equals relation.
        '''
        from proveit.numbers import two
        return ComplexSet.exponentiate_both_sides_of_equals(
            relation, two, assumptions=assumptions)

    @staticmethod
    def square_both_sides_of_notequals(relation,
                                       assumptions=USE_DEFAULTS):
        '''
        Square both sides of the NotEquals relation.
        '''
        from proveit.numbers import two
        return ComplexSet.exponentiate_both_sides_of_notequals(
            relation, two, assumptions=assumptions)

    @staticmethod
    def square_root_both_sides_of_equals(relation, assumptions=USE_DEFAULTS):
        '''
        Take the square root of both sides of the Equals relation.
        '''
        from proveit.numbers import frac, one, two
        new_rel = ComplexSet.exponentiate_both_sides_of_equals(
            relation, frac(one, two), assumptions=assumptions)
        new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel

    @staticmethod
    def square_root_both_sides_of_notequals(relation,
                                            assumptions=USE_DEFAULTS):
        '''
        Take the square root of both sides of the NotEquals relation.
        '''
        from proveit.numbers import frac, one, two
        new_rel = ComplexSet.exponentiate_both_sides_of_notequals(
            relation, frac(one, two), assumptions=assumptions)
        new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel

class ComplexNonZeroSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'ComplexNonZero', r'\mathbb{C}^{\neq 0}',
                           theory=__file__, fence_when_forced=True)

    def membership_side_effects(self, judgment):
        '''
        Yield side-effects when proving 'q in RationalPos'
        for a given q.
        '''
        member = judgment.element
        yield lambda assumptions: self.deduce_member_in_complex(member,
                                                                assumptions)
        yield lambda assumptions: self.deduce_member_not_zero(member, 
                                                              assumptions)
    
    def deduce_member_not_zero(self, member, assumptions=USE_DEFAULTS):
        from . import nonzero_if_in_complex_nonzero
        return nonzero_if_in_complex_nonzero.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_membership_in_bool(self, member, assumptions=USE_DEFAULTS):
        from . import complex_non_zero_membership_is_bool
        from proveit import x
        return complex_non_zero_membership_is_bool.instantiate(
            {x: member}, assumptions=assumptions)

    def deduce_member_in_complex(self, member, assumptions=USE_DEFAULTS):
        from . import complex_non_zero_within_complex
        return complex_non_zero_within_complex.derive_superset_membership(
            member, assumptions)
    

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
