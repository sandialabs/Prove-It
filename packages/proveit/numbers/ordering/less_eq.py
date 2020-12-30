from proveit import Literal, USE_DEFAULTS, as_expression
from proveit.logic import Equals
from proveit import a, b, c, d, x, y, z
from .number_ordering_relation import NumberOrderingRelation

class LessEq(NumberOrderingRelation):
    # operator of the LessEq operation.
    _operator_ = Literal(
        string_format='<=',
        latex_format=r'\leq',
        theory=__file__)

    # map left-hand-sides to "<=" Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to "<=" Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, a, b):
        r'''
        Create an expression representing a <= b.
        '''
        NumberOrderingRelation.__init__(self, LessEq._operator_, a, b)
    
    @staticmethod
    def reversed_operator_str(formatType):
        '''
        Reversing '<=' gives '>='.
        '''
        return r'\geq' if formatType=='latex' else '>=' 

    def reversed(self):
        '''
        Returns this Expression with a reversed inequality style.
        For example, 
            (a <= b).reversed() is b >= a 
            (a >= b).reversed() is b <= a
        '''
        if self.get_style('direction') == 'reversed':
            return self.with_style(direction = 'normal')
        else:
            return self.with_style(direction = 'reversed')
    
    def deduce_in_bool(self, assumptions=frozenset()):
        from . import less_than_equals_is_bool
        is_bool_stmt = less_than_equals_is_bool.instantiate(
            {x: self.lower, y: self.upper}, assumptions=assumptions)
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

    def unfold(self, assumptions=frozenset()):
        from . import less_than_equals_def
        unfolded = less_than_equals_def.instantiate(
                {x: self.lower, y: self.upper}, assumptions=assumptions)
        return unfolded.inner_expr().operands[0].with_matching_style(self)
    
    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this x<=y expression
        and something of the form y<z, y<=z, z>y, z>=y, or y=z to
        obtain x<z or x<=z as appropriate.  In the special case
        of x<=y and y<=x (or x>=y), derive x=z.
        '''
        from . import (transitivity_less_eq_less, transitivity_less_less_eq,
                       transitivity_less_eq_less_eq, symmetric_less_eq)
        from .less import Less
        other = as_expression(other)
        if isinstance(other, Equals):
            return NumberOrderingRelation.apply_transitivity(
                self, other, assumptions)  # handles this special case
        if other.lower == self.upper and other.upper == self.lower:
            # x <= y and y <= x implies that x=y
            return symmetric_less_eq.instantiate(
                {x: self.lower, y: self.upper}, assumptions=assumptions)
        elif other.lower == self.upper:
            if isinstance(other, Less):
                new_rel = transitivity_less_eq_less.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper}, 
                    assumptions=assumptions)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_eq_less_eq.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper}, 
                    assumptions=assumptions)
        elif other.upper == self.lower:
            if isinstance(other, Less):
                new_rel = transitivity_less_less_eq.instantiate(
                    {x: other.lower, y: other.upper, z: self.upper}, 
                    assumptions=assumptions)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_eq_less_eq.instantiate(
                    {x: other.lower, y: other.upper, z: self.upper}, 
                    assumptions=assumptions)
        else:
            raise ValueError(
                "Cannot perform transitivity with %s and %s!" %
                (self, other))
        return new_rel.with_matching_style(self)

    def derive_negated(self, assumptions=frozenset()):
        '''
        From a <= b, derive and return -b <= -a.
        Assumptions may be required to prove that a, and b are in Real.
        '''
        from . import negated_less_eq
        new_rel = negated_less_eq.instantiate(
                {a: self.lower, b: self.upper}, assumptions=assumptions)
        return new_rel.with_matching_style(self)

    def derive_shifted(self, addend, addend_side='right',
            assumptions=USE_DEFAULTS):
        r'''
        From a <= b, derive and return a + c <= b + c
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in
        Real.
        '''
        from . import less_eq_shift_add_right, less_eq_shift_add_left  # , less_than_subtract
        if addend_side == 'right':
            new_rel = less_eq_shift_add_right.instantiate(
                {a: self.lower, b: self.upper, c: addend}, 
                assumptions=assumptions)
        elif addend_side == 'left':
            new_rel = less_eq_shift_add_left.instantiate(
                {a: self.lower, b: self.upper, c: addend}, 
                assumptions=assumptions)
        else:
            raise ValueError(
                "Unrecognized addend side (should be 'left' or 'right'): " +
                str(addend_side))
        return new_rel.with_matching_style(self)
    
    def add_left(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a <= b, derive and return a + c <= b given c <= 0 
        Or from a >= b, derive and return a + c >= b given 0 <= c 
        (and a, b, c are all Real) where c is the given 'addend'.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            new_rel = self.add_right(addend, assumptions)
        else:
            from . import less_eq_add_left
            new_rel = less_eq_add_left.instantiate(
                {a: self.lower, b: self.upper, c: addend},
                assumptions=assumptions)
        return new_rel.with_matching_style(self)

    def add_right(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a <= b, derive and return a <= b + c given 0 <= c 
        Or from a >= b, derive and return a >= b + c given c <= 0 
        (and a, b, c are all Real) where c is the given 'addend'.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            new_rel = self.add_left(addend, assumptions)
        else:
            from . import less_eq_add_right
            new_rel = less_eq_add_right.instantiate(
                {a: self.lower, b: self.upper, c: addend}, 
                assumptions=assumptions)
        return new_rel.with_matching_style(self)

    def add(self, relation, assumptions=USE_DEFAULTS):
        '''
        From a <= b, derive and return a + c <= b + d given c <= d
        (and a, b, c, d are all Real).  c and d are determined from the
        given 'relation'.
        '''
        from . import less_eq_add_both
        from .less import Less
        if not (isinstance(relation, Less) or isinstance(relation, LessEq)):
            raise ValueError("Less.add 'relation' must be of type Less or "
                             "LessEq, not %s"
                             % str(relation.__class__))
        _c = relation.lower
        _d = relation.upper
        new_rel = less_eq_add_both.instantiate(
                {a: self.lower, b: self.upper, c: _c, d: _d},
                assumptions=assumptions)
        return new_rel.with_matching_style(self)
    
    def left_mult_both_sides(self, multiplier, *, simplify=True,
                             assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers import GreaterEq, zero
        from proveit.numbers.multiplication import (
            left_mult_pos_lesseq, left_mult_neg_lesseq)
        if GreaterEq(multiplier, zero).proven(assumptions):
            new_rel = left_mult_pos_lesseq.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(multiplier, zero).proven(assumptions):
            new_rel = left_mult_neg_lesseq.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        else:
            raise Exception(
                "Cannot 'left_mult_both_sides' a LessEq relation without "
                "knowing the multiplier's relation with zero.")
        return new_rel.with_matching_style(self)

    def right_mult_both_sides(self, multiplier, *, simplify=True,
                              assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers import zero
        from proveit.numbers.multiplication import (
            right_mult_pos_lesseq, right_mult_neg_lesseq)
        if LessEq(zero, multiplier).proven(assumptions):
            new_rel = right_mult_pos_lesseq.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(multiplier, zero).proven(assumptions):
            new_rel = right_mult_neg_lesseq.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        else:
            raise Exception(
                "Cannot 'right_mult_both_sides' a LessEq relation without "
                "knowing the multiplier's relation with zero.")
        return new_rel.with_matching_style(self)

    def divide_both_sides(self, divisor, *, simplify=True,
                          assumptions=USE_DEFAULTS):
        '''
        Divide both sides of the relation by the 'divisor'.
        '''
        from proveit.numbers import Less, zero
        from proveit.numbers.division import (
            div_pos_lesseq, div_neg_lesseq)
        if Less(zero, divisor).proven(assumptions):
            new_rel = div_pos_lesseq.instantiate(
                {a: divisor, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif Less(divisor, zero).proven(assumptions):
            new_rel = div_neg_lesseq.instantiate(
                {a: divisor, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        else:
            raise Exception("Cannot 'divide' a LessEq relation without "
                            "knowing whether the divisor is greater than "
                            "or less than zero.")
        return new_rel.with_matching_style(self)

    def left_add_both_sides(self, addend, *, simplify=True,
                            assumptions=USE_DEFAULTS):
        '''
        Add to both sides of the relation by the 'addend' on the left.
        '''
        from proveit.numbers.addition import left_add_lesseq
        new_rel = left_add_lesseq.instantiate(
            {a: addend, x: self.lower, y: self.upper},
            assumptions=assumptions)._simplify_both_sides(
            simplify=simplify, assumptions=assumptions)
        return new_rel.with_matching_style(self)

    def right_add_both_sides(self, addend, *, simplify=True,
                             assumptions=USE_DEFAULTS):
        '''
        Add to both sides of the relation by the 'addend' on the right.
        '''
        from proveit.numbers.addition import right_add_lesseq
        new_rel = right_add_lesseq.instantiate(
            {a: addend, x: self.lower, y: self.upper},
            assumptions=assumptions)._simplify_both_sides(
            simplify=simplify, assumptions=assumptions)
        return new_rel.with_matching_style(self)

    def exponentiate_both_sides(self, exponent, *, simplify=True,
                                assumptions=USE_DEFAULTS):
        '''
        Exponentiate both sides of the relation by the 'exponent'.
        '''
        from proveit.numbers import Less, zero
        from proveit.numbers.exponentiation import (
            exp_pos_lesseq, exp_nonneg_lesseq,
            exp_neg_lesseq, exp_nonpos_lesseq)
        if Less(exponent, zero).proven(assumptions):
            new_rel = exp_pos_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif Less(exponent, zero).proven(assumptions):
            new_rel = exp_neg_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(exponent, zero).proven(assumptions):
            new_rel = exp_nonneg_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(exponent, zero).proven(assumptions):
            new_rel = exp_nonpos_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)  ._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        else:
            raise Exception("Cannot 'exponentiate' a Less relation without "
                            "knowing the exponent's relation with zero")
        return new_rel.with_matching_style(self)


def greater_eq(a, b):
    '''
    Return an expression representing a >= b, internally represented 
    as b <= a but with a style that reverses the direction.    
    '''
    return LessEq(b, a).with_style(direction='reversed')
