from proveit import (Literal, Operation, USE_DEFAULTS, as_expression,
                     UnsatisfiedPrerequisites)
from proveit.logic import Equals
from proveit import a, b, c, d, x, y, z
from .number_ordering_relation import NumberOrderingRelation

class Less(NumberOrderingRelation):
    # operator of the Less operation.
    _operator_ = Literal(string_format='<', theory=__file__)

    # map left-hand-sides to "<" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_left_sides = dict()
    # map right-hand-sides to "<" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_right_sides = dict()

    def __init__(self, lhs, rhs):
        r'''
        Create an expression of the form lhs < rhs.
        '''
        NumberOrderingRelation.__init__(self, Less._operator_, lhs, rhs)
    
    def side_effects(self, judgment):
        '''
        In addition to the NumberOrderingRelation side-effects, also
        derive a ≠ b from a < b as a side-effect.
        '''
        for side_effect in NumberOrderingRelation.side_effects(
                self, judgment):
            yield side_effect
        yield self.derive_not_equal
        
    @staticmethod
    def reversed_operator_str(formatType):
        '''
        Reversing '<' gives '>'.
        '''
        return '>' 
    
    def remake_constructor(self):
        if self.is_reversed():
            # Use the 'greater' function if it is reversed.
            return 'greater'
        # Use the default.
        return Operation.remake_constructor(self)
    
    def conclude(self, assumptions):
        '''
        Conclude something of the form 
        a < b.
        '''
        from proveit.logic import InSet
        from proveit.numbers import Add, zero, RealPos
        from . import positive_if_real_pos
        if self.upper == zero:
            # Special case with upper bound of zero.
            from . import negative_if_real_neg
            concluded = negative_if_real_neg.instantiate(
                {a: self.lower}, assumptions=assumptions)
            return concluded.with_matching_style(self)            
        if self.lower == zero:
            # Special case with lower bound of zero.
            if InSet(self.upper, RealPos).proven(assumptions):
                positive_if_real_pos.instantiate({a: self.upper},
                                                 assumptions=assumptions)
        if ((isinstance(self.lower, Add) and 
                self.upper in self.lower.terms.entries) or
             (isinstance(self.upper, Add) and 
                self.lower in self.upper.terms.entries)):
            try:
                # Conclude an sum is bounded by one of its terms.
                return self.conclude_as_bounded_by_term(assumptions)
            except UnsatisfiedPrerequisites:
                # If prerequisites weren't satisfied to do this,
                # we can still try something else.
                pass
        return NumberOrderingRelation.conclude(self, assumptions)
    
    def conclude_as_bounded_by_term(self, assumptions=USE_DEFAULTS):
        '''
        Conclude something of the form
            a_1 + ... + a_i + b + c_1 + ... + c_j > b 
            assuming a_1, ..., a_i and c_1, ..., c_j all in RealPos
                and i + j > 0
        or
            a_1 + ... + a_i + b + c_1 + ... + c_j < b 
            assuming a_1, ..., a_i and c_1, ..., c_j all in RealNeg
                and i + j > 0
        '''
        from proveit.numbers import Add, one
        from proveit.numbers.ordering import (less_than_successor, 
                                              less_than_left_successor,
                                              less_than_an_increase,
                                              less_than_an_left_increase)
        if (isinstance(self.lower, Add) and 
                self.upper in self.lower.terms.entries):
            concluded = self.lower.deduce_bound_by_term(self.upper, assumptions)
        elif (isinstance(self.upper, Add) and 
                self.lower in self.upper.terms.entries):
            if self.upper.terms.is_double():
                # special binary cases
                if self.lower == self.upper.terms[0]:
                    if self.upper.terms[1] == one:
                        # a + 1 > a
                        concluded = less_than_successor.instantiate(
                                {a: self.lower}, assumptions=assumptions)
                    else:
                        # a + b > a assuming b in RealPos
                        concluded = less_than_an_increase.instantiate(
                            {a: self.lower, b: self.upper.terms[1]}, 
                            assumptions=assumptions)
                else:
                    assert self.lower == self.upper.terms[1]
                    if self.upper.terms[0] == one:
                        # 1 + a > a
                        concluded = less_than_left_successor.instantiate(
                                {a: self.lower}, assumptions=assumptions)
                    else:
                        # b + a > a assuming b in RealPos
                        concluded = less_than_an_left_increase.instantiate(
                            {a: self.lower, b: self.upper.terms[0]}, 
                            assumptions=assumptions)                    
            else:
                concluded = self.upper.deduce_bound_by_term(self.lower, assumptions)
        else:
            raise ValueError("Less.conclude_as_bounded_by_term is only "
                             "applicable if one side of the Less "
                             "expression is an addition and the other "
                             "side is one of the terms")
        return concluded.with_matching_style(self)

    def conclude_via_equality(self, assumptions=USE_DEFAULTS):
        from . import relax_equal_to_less_eq
        concluded = relax_equal_to_less_eq.instantiate(
            {x: self.operands[0], y: self.operands[1]},
            assumptions=assumptions)
        return concluded.with_matching_style(self)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        from . import less_than_is_bool
        is_bool_stmt = less_than_is_bool.instantiate(
            {x: self.lower, y: self.upper}, assumptions=assumptions)
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

    def derive_relaxed(self, assumptions=USE_DEFAULTS):
        '''
        Relax a < b to a <= b, deducing the latter from the former 
        (self) and returning the latter.  Assumptions may be required 
        to deduce that a and b are in Real.
        '''
        from . import relax_less
        new_rel = relax_less.instantiate(
            {x: self.lower, y: self.upper}, assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def derive_not_equal(self, assumptions=USE_DEFAULTS):
        '''
        Derive a ≠ b from a < b.
        '''
        from proveit.numbers.ordering import less_is_not_eq
        _a, _b = self.lower, self.upper
        return less_is_not_eq.instantiate(
            {a: _a, b: _b}, assumptions=assumptions)

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this x<y expression
        and something of the form y<z, y<=z, z>y, z>=y, or y=z to
        obtain x<z.
        '''
        from . import transitivity_less_less
        from . import transitivity_less_less_eq
        from . import transitivity_less_eq_less
        from .less_eq import LessEq
        other = as_expression(other)
        if isinstance(other, Equals):
            return NumberOrderingRelation.apply_transitivity(
                self, other, assumptions)  # handles this special case
        elif other.lower == self.upper:
            if isinstance(other, Less):
                new_rel = transitivity_less_less.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper}, 
                    assumptions=assumptions)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_less_eq.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper}, 
                    assumptions=assumptions)
        elif other.upper == self.lower:
            if isinstance(other, Less):
                new_rel = transitivity_less_less.instantiate(
                    {x: other.lower, y: self.lower, z: self.upper}, 
                    assumptions=assumptions)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_eq_less.instantiate(
                    {x: other.lower, y: self.lower, z: self.upper}, 
                    assumptions=assumptions)
        else:
            raise ValueError(
                "Cannot perform transitivity with %s and %s!" %
                (self, other))
        return new_rel.with_mimicked_style(self)

    """
    def derive_negated(self, assumptions=frozenset()):
        '''
        From :math:`a < b`, derive and return :math:`-a > -b`.
        Assumptions may be required to prove that a, and b are in Real.
        '''
        from . import negated_less_than
        return negated_less_than.instantiate({a:self.lower, b:self.upper})
    """

    def derive_shifted(self, addend, addend_side='right',
                       assumptions=USE_DEFAULTS):
        r'''
        From a < b, derive and return a + c < b + c
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in
        Real.
        '''
        from . import less_shift_add_right, less_shift_add_left
        if addend_side == 'right':
            new_rel = less_shift_add_right.instantiate(
                {a: self.lower, b: self.upper, c: addend}, 
                assumptions=assumptions)
        elif addend_side == 'left':
            new_rel = less_shift_add_left.instantiate(
                {a: self.lower, b: self.upper, c: addend}, 
                assumptions=assumptions)
        else:
            raise ValueError(
                "Unrecognized addend side (should be 'left' or 'right'): " +
                str(addend_side))
        return new_rel.with_mimicked_style(self)

    def add_left(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a < b, derive and return a + c < b given c <= 0 
        Or from a > b, derive and return a + c > b given 0 <= c 
        (and a, b, c are all Real) where c is the given 'addend'.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            new_rel = self.add_right(addend, assumptions)
        else:
            from . import less_add_left
            new_rel = less_add_left.instantiate(
                    {a: self.lower, b: self.upper, c: addend},
                    assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def add_right(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a < b, derive and return a < b + c given 0 <= c 
        Or from a > b, derive and return a > b + c given c <= 0 
        (and a, b, c are all Real) where c is the given 'addend'.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            new_rel = self.add_left(addend, assumptions)
        else:
            from . import less_add_right
            new_rel = less_add_right.instantiate(
                {a: self.lower, b: self.upper, c: addend}, 
                assumptions=assumptions)
        return new_rel.with_mimicked_style(self)
    
    def add(self, relation, assumptions=USE_DEFAULTS):
        '''
        From a < b, derive and return a + c < b + d given c < d or 
        given c <= d (and a, b, c, d are all Real).  c and d are 
        determined from the given 'relation'.
        '''
        from . import less_add_both
        from .less_eq import LessEq
        if not (isinstance(relation, Less) or isinstance(relation, LessEq)):
            raise ValueError("Less.add 'relation' must be of type Less or "
                             "LessEq, not %s"
                             % str(relation.__class__))
        _c = relation.lower
        _d = relation.upper
        new_rel = less_add_both.instantiate(
                {a: self.lower, b: self.upper, c: _c, d: _d},
                assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def left_mult_both_sides(self, multiplier, *, simplify=True,
                             assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers import Less, LessEq, zero
        from proveit.numbers.multiplication import (
            left_mult_pos_less, left_mult_nonneg_less,
            left_mult_neg_less, left_mult_nonpos_less)
        if Less(zero, multiplier).proven(assumptions):
            new_rel = left_mult_pos_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif Less(multiplier, zero).proven(assumptions):
            new_rel = left_mult_neg_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(zero, multiplier).proven(assumptions):
            new_rel = left_mult_nonneg_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(multiplier, zero).proven(assumptions):
            new_rel = left_mult_nonpos_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        else:
            raise Exception(
                "Cannot 'left_mult_both_sides' a Less relation without "
                "knowing the multiplier's relation with zero.")
        return new_rel.with_mimicked_style(self)

    def right_mult_both_sides(self, multiplier, *, simplify=True,
                              assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers import LessEq, zero
        from proveit.numbers.multiplication import (
            right_mult_pos_less, right_mult_nonneg_less,
            right_mult_neg_less, right_mult_nonpos_less)
        if Less(zero, multiplier).proven(assumptions):
            new_rel = right_mult_pos_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif Less(multiplier, zero).proven(assumptions):
            new_rel = right_mult_neg_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(zero, multiplier).proven(assumptions):
            new_rel = right_mult_nonneg_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(multiplier, zero).proven(assumptions):
            new_rel = right_mult_nonpos_less.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        else:
            raise Exception(
                "Cannot 'right_mult_both_sides' a Less relation without "
                "knowing the multiplier's relation with zero.")
        return new_rel.with_mimicked_style(self)

    def divide_both_sides(self, divisor, *, simplify=True,
                          assumptions=USE_DEFAULTS):
        '''
        Divide both sides of the relation by the 'divisor'.
        '''
        from proveit.numbers import Less, zero
        from proveit.numbers.division import (
            strong_div_from_numer_bound__pos_denom, 
            strong_div_from_numer_bound__neg_denom)
        if Less(zero, divisor).proven(assumptions):
            thm = strong_div_from_numer_bound__pos_denom
        elif Less(divisor, zero).proven(assumptions):
            thm = strong_div_from_numer_bound__neg_denom
        else:
            raise Exception("Cannot 'divide' a Less relation without "
                            "knowing whether the divisor is greater than "
                            "or less than zero.")
        new_rel = thm.instantiate(
                {a: divisor, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def left_add_both_sides(self, addend, *, simplify=True,
                            assumptions=USE_DEFAULTS):
        '''
        Add to both sides of the relation by the 'addend' on the left.
        '''
        from proveit.numbers.addition import strong_bound_by_right_term
        new_rel = strong_bound_by_right_term.instantiate(
            {a: addend, x: self.lower, y: self.upper},
            assumptions=assumptions)._simplify_both_sides(
            simplify=simplify, assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def right_add_both_sides(self, addend, *, simplify=True,
                             assumptions=USE_DEFAULTS):
        '''
        Add to both sides of the relation by the 'addend' on the right.
        '''
        from proveit.numbers.addition import strong_bound_by_left_term
        new_rel = strong_bound_by_left_term.instantiate(
            {a: addend, x: self.lower, y: self.upper},
            assumptions=assumptions)._simplify_both_sides(
            simplify=simplify, assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def exponentiate_both_sides(self, exponent, *, simplify=True,
                                assumptions=USE_DEFAULTS):
        '''
        Exponentiate both sides of the relation by the 'exponent'.
        '''
        from proveit.numbers import Less, LessEq, zero
        from proveit.numbers.exponentiation import (
            exp_pos_less, exp_nonneg_less, exp_neg_less, exp_nonpos_less)
        if Less(zero, exponent).proven(assumptions):
            new_rel = exp_pos_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif Less(exponent, zero).proven(assumptions):
            new_rel = exp_neg_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(zero, exponent).proven(assumptions):
            new_rel = exp_nonneg_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(exponent, zero).proven(assumptions):
            new_rel = exp_nonpos_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        else:
            raise Exception("Cannot 'exponentiate' a Less relation without "
                            "knowing the exponent's relation with zero")
        return new_rel.with_mimicked_style(self)


def greater(a, b):
    '''
    Return an expression representing a > b, internally represented 
    as b < a but with a style that reverses the direction.    
    '''
    return Less(b, a).with_styles(direction='reversed')
