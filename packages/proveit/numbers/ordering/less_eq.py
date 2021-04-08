from proveit import (Literal, Operation, USE_DEFAULTS, as_expression,
                     UnsatisfiedPrerequisites)
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

    def __init__(self, a, b, *, styles=None):
        r'''
        Create an expression representing a <= b.
        '''
        NumberOrderingRelation.__init__(self, LessEq._operator_, a, b,
                                        styles=styles)

    @staticmethod
    def reversed_operator_str(formatType):
        '''
        Reversing '<=' gives '>='.
        '''
        return r'\geq' if formatType=='latex' else '>=' 

    def remake_constructor(self):
        if self.is_reversed():
            # Use the 'greater_eq' function if it is reversed.
            return 'greater_eq'
        # Use the default.
        return Operation.remake_constructor(self)

    def conclude(self, assumptions):
        '''
        Conclude something of the form 
        a ≤ b.
        '''
        from proveit.logic import InSet
        from proveit.numbers import Add, zero, RealNonNeg
        from . import non_neg_if_real_non_neg
        if Equals(self.lower, self.upper).proven(assumptions):
            # We know that a = b, therefore a ≤ b.
            return self.conclude_via_equality(assumptions)
        if self.upper == zero:
            # Special case with upper bound of zero.
            from . import non_pos_if_real_non_pos
            concluded = non_pos_if_real_non_pos.instantiate(
                {a: self.lower}, assumptions=assumptions)
            return concluded.with_matching_style(self)            
        if self.lower == zero:
            # Special case with lower bound of zero.
            if InSet(self.upper, RealNonNeg).proven(assumptions):
                return non_neg_if_real_non_neg.instantiate(
                        {a: self.upper}, assumptions=assumptions)
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

    def conclude_via_equality(self, assumptions=USE_DEFAULTS):
        '''
        Conclude a ≤ b from a = b.
        '''
        from . import relax_equal_to_less_eq
        return relax_equal_to_less_eq.instantiate(
            {x: self.operands[0], y: self.operands[1]},
            assumptions=assumptions)

    def conclude_as_bounded_by_term(self, assumptions=USE_DEFAULTS):
        '''
        Conclude something of the form
            a_1 + ... + a_i + b + c_1 + ... + c_j ≥ b 
            assuming a_1, ..., a_i and c_1, ..., c_j all in RealNonNeg
        or
            a_1 + ... + a_i + b + c_1 + ... + c_j ≤ b 
            assuming a_1, ..., a_i and c_1, ..., c_j all in RealNonPos
        '''
        from proveit.numbers import Add
        if (isinstance(self.lower, Add) and 
                self.upper in self.lower.terms.entries):
            return self.lower.bound_by_term(self.upper, assumptions)
        elif (isinstance(self.upper, Add) and 
                self.lower in self.upper.terms.entries):
            return self.upper.bound_by_term(self.lower, assumptions)
        else:
            raise ValueError("LessEq.conclude_as_bounded_by_term is only "
                             "applicable if one side of the Less "
                             "expression is an addition and the other "
                             "side is one of the terms")
    
    def deduce_in_bool(self, assumptions=frozenset()):
        from . import less_than_equals_is_bool
        is_bool_stmt = less_than_equals_is_bool.instantiate(
            {x: self.lower, y: self.upper}, assumptions=assumptions)
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

    def unfold(self, assumptions=frozenset()):
        from . import less_eq_def
        unfolded = less_eq_def.instantiate(
                {x: self.lower, y: self.upper}, assumptions=assumptions)
        return unfolded.inner_expr().operands[0].with_mimicked_style(self)
    
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
        return new_rel.with_mimicked_style(self)

    def derive_negated(self, assumptions=frozenset()):
        '''
        From a <= b, derive and return -b <= -a.
        Assumptions may be required to prove that a, and b are in Real.
        '''
        from . import negated_less_eq
        new_rel = negated_less_eq.instantiate(
                {a: self.lower, b: self.upper}, assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

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
        return new_rel.with_mimicked_style(self)
    
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
        return new_rel.with_mimicked_style(self)

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
        return new_rel.with_mimicked_style(self)

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
        return new_rel.with_mimicked_style(self)
    
    def left_mult_both_sides(self, multiplier, *, simplify=True,
                             assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers import greater_eq, zero
        from proveit.numbers.multiplication import (
            weak_bound_via_right_factor_bound,
            reversed_weak_bound_via_right_factor_bound)
        was_reversed = False
        if greater_eq(multiplier, zero).proven(assumptions):
            new_rel = weak_bound_via_right_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(multiplier, zero).proven(assumptions):
            new_rel = reversed_weak_bound_via_right_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
            was_reversed = True
        else:
            raise Exception(
                "Cannot left-multiply both sides of %s by %s "
                "without knowing the multiplier's relation with zero."
                %(self, multiplier))
        new_rel = new_rel.with_mimicked_style(self)
        if was_reversed:
            new_rel = new_rel.with_direction_reversed()
        return new_rel

    def right_mult_both_sides(self, multiplier, *, simplify=True,
                              assumptions=USE_DEFAULTS):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers import zero
        from proveit.numbers.multiplication import (
            weak_bound_via_left_factor_bound,
            reversed_weak_bound_via_left_factor_bound)
        was_reversed = False
        if LessEq(zero, multiplier).proven(assumptions):
            new_rel = weak_bound_via_left_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(multiplier, zero).proven(assumptions):
            new_rel = reversed_weak_bound_via_left_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
            was_reversed = True
        else:
            raise Exception(
                "Cannot right-multiply both sides of %s by %s "
                "without knowing the multiplier's relation with zero."
                %(self, multiplier))
        new_rel = new_rel.with_mimicked_style(self)
        if was_reversed:
            new_rel = new_rel.with_direction_reversed()
        return new_rel

    def divide_both_sides(self, divisor, *, simplify=True,
                          assumptions=USE_DEFAULTS):
        '''
        Divide both sides of the relation by the 'divisor'.
        '''
        from proveit.numbers import Less, zero
        from proveit.numbers.division import (
            weak_div_from_numer_bound__pos_denom, 
            weak_div_from_numer_bound__neg_denom)
        if Less(zero, divisor).proven(assumptions):
            thm = weak_div_from_numer_bound__pos_denom
        elif Less(divisor, zero).proven(assumptions):
            thm = weak_div_from_numer_bound__neg_denom
        else:
            raise Exception("Cannot divide both sides of %s by %s "
                            "without knowing the divisors "
                            "relation to zero."%(self, divisor))
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
        from proveit.numbers.addition import weak_bound_via_right_term_bound
        new_rel = weak_bound_via_right_term_bound.instantiate(
            {a: addend, x: self.lower, y: self.upper},
            assumptions=assumptions)._simplify_both_sides(
            simplify=simplify, assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def right_add_both_sides(self, addend, *, simplify=True,
                             assumptions=USE_DEFAULTS):
        '''
        Add to both sides of the relation by the 'addend' on the right.
        '''
        from proveit.numbers.addition import weak_bound_via_left_term_bound
        new_rel = weak_bound_via_left_term_bound.instantiate(
            {a: addend, x: self.lower, y: self.upper},
            assumptions=assumptions)._simplify_both_sides(
            simplify=simplify, assumptions=assumptions)
        return new_rel.with_mimicked_style(self)

    def exponentiate_both_sides(self, exponent, *, simplify=True,
                                assumptions=USE_DEFAULTS):
        '''
        Exponentiate both sides of the relation by the 'exponent'.
        '''
        from proveit.numbers import Less, zero
        from proveit.numbers.exponentiation import (
            exp_pos_lesseq, exp_nonneg_lesseq,
            exp_neg_lesseq, exp_nonpos_lesseq)
        # We need to know how the exponent relates to zero.
        LessEq.sort([zero, exponent], assumptions)
        if Less(zero, exponent).proven(assumptions):
            new_rel = exp_pos_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif Less(exponent, zero).proven(assumptions):
            new_rel = exp_neg_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper},
                assumptions=assumptions)._simplify_both_sides(
                simplify=simplify, assumptions=assumptions)
        elif LessEq(zero, exponent).proven(assumptions):
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
            raise Exception("Cannot exponentiate both sides of %s by %s "
                            "without knowing the exponent's relation with "
                            "zero"%(self, exponent))
        return new_rel.with_mimicked_style(self)


def greater_eq(a, b):
    '''
    Return an expression representing a >= b, internally represented 
    as b <= a but with a style that reverses the direction.    
    '''
    return LessEq(b, a).with_styles(direction='reversed')
