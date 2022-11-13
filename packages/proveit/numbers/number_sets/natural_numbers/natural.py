import proveit
from proveit import prover, maybe_fenced_string
from proveit.numbers.number_sets.number_set import NumberSet
from proveit import a, n, x, y
from proveit.logic import Equals, NotEquals


class NaturalSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Natural', r'\mathbb{N}', 
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .natural_membership import NaturalMembership    
        return NaturalMembership(element, self)

    @staticmethod
    @prover
    def left_add_both_sides_of_equals(relation, addend,
                                      **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the left.
        '''
        from proveit.numbers.addition import left_add_eq_nat
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_add_eq_nat.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_add_both_sides_of_notequals(relation, addend,
                                         **defaults_config):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the left.
        '''
        from proveit.numbers.addition import left_add_neq_nat
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_add_neq_nat.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_add_both_sides_of_equals(relation, addend,
                                       **defaults_config):
        '''
        Add both sides of the Equals relation by the 'addend'
        on the right.
        '''
        from proveit.numbers.addition import right_add_eq_nat
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_add_eq_nat.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_add_both_sides_of_notequals(relation, addend,
                                          **defaults_config):
        '''
        Add both sides of the NotEquals relation by the 'addend'
        on the right.
        '''
        from proveit.numbers.addition import right_add_neq_nat
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_add_neq_nat.instantiate(
            {a: addend, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_mult_both_sides_of_equals(relation, multiplier,
                                       **defaults_config):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers.multiplication import left_mult_eq_nat
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return left_mult_eq_nat.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def left_mult_both_sides_of_notequals(relation, multiplier,
                                          **defaults_config):
        '''
        Multiply both sides of a NonEquals relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers.multiplication import left_mult_neq_nat
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return left_mult_neq_nat.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_mult_both_sides_of_equals(relation, multiplier,
                                        **defaults_config):
        '''
        Multiply both sides of an Equals relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers.multiplication import right_mult_eq_nat
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return right_mult_eq_nat.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def right_mult_both_sides_of_notequals(relation, multiplier,
                                           **defaults_config):
        '''
        Multiply both sides of a NotEquals relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers.multiplication import right_mult_neq_nat
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return right_mult_neq_nat.instantiate(
            {a: multiplier, x: relation.lhs, y: relation.rhs})


    @staticmethod
    @prover
    def divide_both_sides_of_equals(relation, divisor,
                                    **defaults_config):
        '''
        Divide both sides of the Equals relation by the 'divisor'.
        '''
        from proveit.numbers.division import div_eq_nat
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return div_eq_nat.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def divide_both_sides_of_notequals(relation, divisor, 
                                       **defaults_config):
        '''
        Divide both sides of the NotEquals relation by the 'divisor'.
        '''
        from proveit.numbers.division import div_neq_nat
        if not isinstance(relation, NotEquals):
            TypeError("'relation' expected to be NotEquals")
        return div_neq_nat.instantiate(
            {a: divisor, x: relation.lhs, y: relation.rhs})

    @staticmethod
    @prover
    def exponentiate_both_sides_of_equals(relation, exponent,
                                          **defaults_config):
        '''
        Add both sides of the Equals relation by the 'exponent'.
        '''
        from proveit.numbers.exponentiation import exp_eq_nat
        if not isinstance(relation, Equals):
            TypeError("'relation' expected to be Equals")
        return exp_eq_nat.instantiate(
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
        return NaturalSet.exponentiate_both_sides_of_equals(
            relation, two)

    @staticmethod
    @prover
    def square_both_sides_of_notequals(relation, **defaults_config):
        '''
        Square both sides of the NotEquals relation.
        '''
        from proveit.numbers import two
        return NaturalSet.exponentiate_both_sides_of_notequals(
            relation, two)

    @staticmethod
    @prover
    def square_root_both_sides_of_equals(relation, **defaults_config):
        '''
        Take the square root of both sides of the Equals relation.
        '''
        from proveit.numbers import frac, one, two, Exp
        new_rel = NaturalSet.exponentiate_both_sides_of_equals(
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
        new_rel = NaturalSet.exponentiate_both_sides_of_notequals(
            relation, frac(one, two))
        new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        return new_rel


class NaturalPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(
            self, 'NaturalPos', r'\mathbb{N}^+',
            theory=__file__, styles=styles)

    def membership_object(self, element):
        from .natural_membership import NaturalPosMembership    
        return NaturalPosMembership(element)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an example of
        # when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an example of
        # when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)



if proveit.defaults.running_theory_notebook is None:
    # Import some fundamental theorems without quantifiers when not 
    # running an common/axioms/theorems theory notebook.
    from . import zero_set_within_nat, nat_pos_within_nat
