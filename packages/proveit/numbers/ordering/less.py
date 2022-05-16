from proveit import (Literal, Operation, USE_DEFAULTS, as_expression,
                     UnsatisfiedPrerequisites, prover, relation_prover)
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

    # map canonical left hand sides to '<' Judgments paired with
    # canonical left hand sides.
    known_canonical_bounds = dict()


    def __init__(self, lhs, rhs, *, styles=None):
        r'''
        Create an expression of the form lhs < rhs.
        '''
        NumberOrderingRelation.__init__(self, Less._operator_, lhs, rhs,
                                        styles=styles)
    
    def side_effects(self, judgment):
        '''
        In addition to the NumberOrderingRelation side-effects, also
        derive a ≠ b from a < b as a side-effect.
        '''
        # Remember the canonical bound.
        canonical_form = self.canonical_form()
        known_canonical_bounds = Less.known_canonical_bounds
        known_canonical_bounds.setdefault(canonical_form.lhs, set()).add(
                (judgment, canonical_form.rhs))
        for side_effect in NumberOrderingRelation.side_effects(
                self, judgment):
            yield side_effect
        yield self.derive_not_equal
        yield self.deduce_complement

    def negation_side_effects(self, judgment):
        '''
        From Not(a < b) derive a >= b as a side-effect.
        '''
        yield self.deduce_complement_of_complement
        
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
    
    @prover
    def conclude(self, **defaults_config):
        '''
        Conclude something of the form 
        a < b.
        '''
        from proveit.logic import InSet
        from proveit.numbers import Add, zero, RealPos, deduce_number_set
        from . import positive_if_real_pos
        try:
            # If there is a known bound that is similar and at least
            # as strong, we can derive this bound from the known one.
            return self.conclude_from_known_bound()
        except UnsatisfiedPrerequisites:
            pass
        if self.upper == zero:
            # Special case with upper bound of zero.
            from . import negative_if_real_neg
            concluded = negative_if_real_neg.instantiate(
                {a: self.lower})
            return concluded
        if self.lower == zero:
            # Special case with lower bound of zero.
            deduce_number_set(self.upper)
            if InSet(self.upper, RealPos).proven():
                positive_if_real_pos.instantiate({a: self.upper})
        if ((isinstance(self.lower, Add) and 
                self.upper in self.lower.terms.entries) or
             (isinstance(self.upper, Add) and 
                self.lower in self.upper.terms.entries)):
            try:
                # Conclude an sum is bounded by one of its terms.
                return self.conclude_as_bounded_by_term()
            except UnsatisfiedPrerequisites:
                # If prerequisites weren't satisfied to do this,
                # we can still try something else.
                pass
        return NumberOrderingRelation.conclude(self)
    
    @prover
    def conclude_as_bounded_by_term(self, **defaults_config):
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
            concluded = self.lower.bound_by_term(self.upper)
        elif (isinstance(self.upper, Add) and 
                self.lower in self.upper.terms.entries):
            if self.upper.terms.is_double():
                # special binary cases
                if self.lower == self.upper.terms[0]:
                    if self.upper.terms[1] == one:
                        # a + 1 > a
                        concluded = less_than_successor.instantiate(
                                {a: self.lower})
                    else:
                        # a + b > a assuming b in RealPos
                        concluded = less_than_an_increase.instantiate(
                            {a: self.lower, b: self.upper.terms[1]})
                else:
                    assert self.lower == self.upper.terms[1]
                    if self.upper.terms[0] == one:
                        # 1 + a > a
                        concluded = less_than_left_successor.instantiate(
                                {a: self.lower})
                    else:
                        # b + a > a assuming b in RealPos
                        concluded = less_than_an_left_increase.instantiate(
                            {a: self.lower, b: self.upper.terms[0]})                    
            else:
                concluded = self.upper.bound_by_term(self.lower)
        else:
            raise ValueError("Less.conclude_as_bounded_by_term is only "
                             "applicable if one side of the Less "
                             "expression is an addition and the other "
                             "side is one of the terms")
        return concluded

    @prover
    def conclude_via_equality(self, **defaults_config):
        from . import relax_equal_to_less_eq
        concluded = relax_equal_to_less_eq.instantiate(
            {x: self.operands[0], y: self.operands[1]})
        return concluded
    
    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import less_than_is_bool
        is_bool_stmt = less_than_is_bool.instantiate(
            {x: self.lower, y: self.upper})
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

    @prover
    def derive_relaxed(self, **defaults_config):
        '''
        Relax a < b to a <= b, deducing the latter from the former 
        (self) and returning the latter.  Assumptions may be required 
        to deduce that a and b are in Real.
        '''
        from . import relax_less
        new_rel = relax_less.instantiate(
            {x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    @prover
    def derive_not_equal(self, **defaults_config):
        '''
        Derive a ≠ b from a < b.
        '''
        from proveit.numbers.ordering import less_is_not_eq
        _a, _b = self.lower, self.upper
        return less_is_not_eq.instantiate({a: _a, b: _b})

    @prover
    def apply_transitivity(self, other, **defaults_config):
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
                self, other)  # handles this special case
        elif other.lower == self.upper:
            if isinstance(other, Less):
                new_rel = transitivity_less_less.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper},
                    preserve_all=True)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_less_eq.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper},
                    preserve_all=True)
        elif other.upper == self.lower:
            if isinstance(other, Less):
                new_rel = transitivity_less_less.instantiate(
                    {x: other.lower, y: self.lower, z: self.upper},
                    preserve_all=True)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_eq_less.instantiate(
                    {x: other.lower, y: self.lower, z: self.upper},
                    preserve_all=True)
        else:
            raise ValueError(
                "Cannot perform transitivity with %s and %s!" %
                (self, other))
        return new_rel.with_mimicked_style(self)

    @prover
    def derive_negated(self, **defaults_config):
        '''
        From a < b, derive and return -b < -a.
        '''
        from proveit.numbers.negation import negated_strong_bound
        new_rel = negated_strong_bound.instantiate(
                {x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    # Temporarily leaving the original here while testing continues.
    # @prover
    # def deduce_complement(self, **defaults_config):
    #     '''
    #     From Not(a < b), derive and return b <= a.
    #     '''
    #     from . import less_complement_is_greater_eq
    #     return less_complement_is_greater_eq.instantiate(
    #             {x:self.lower, y:self.upper}).derive_consequent()

    @prover
    def deduce_complement(self, **defaults_config):
        '''
        From a < b, derive and return Not(b <= a).
        '''
        from . import not_less_eq_from_less
        return not_less_eq_from_less.instantiate(
                {x:self.lower, y:self.upper})

    @prover
    def deduce_complement_of_complement(self, **defaults_config):
        '''
        From Not(a < b), derive and return b <= a.
        '''
        from . import less_eq_from_not_less
        return less_eq_from_not_less.instantiate(
                {x:self.lower, y:self.upper})

    @prover
    def shallow_simplification_of_negation(self, **defaults_config):
        '''
        Prove and return Not(a < b) = (b <= a) as a simplification.
        '''
        from . import less_complement_is_greater_eq
        return less_complement_is_greater_eq.instantiate(
                {x:self.lower, y:self.upper})  

    @prover
    def derive_shifted(self, addend, addend_side='right',
                       **defaults_config):
        r'''
        From a < b, derive and return a + c < b + c
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in
        Real.
        '''
        from . import less_shift_add_right, less_shift_add_left
        if addend_side == 'right':
            new_rel = less_shift_add_right.instantiate(
                {a: self.lower, b: self.upper, c: addend})
        elif addend_side == 'left':
            new_rel = less_shift_add_left.instantiate(
                {a: self.lower, b: self.upper, c: addend})
        else:
            raise ValueError(
                "Unrecognized addend side (should be 'left' or 'right'): " +
                str(addend_side))
        return new_rel.with_mimicked_style(self)

    @prover
    def add_left(self, addend, **defaults_config):
        '''
        From a < b, derive and return a + c < b given c <= 0 
        Or from a > b, derive and return a + c > b given 0 <= c 
        (and a, b, c are all Real) where c is the given 'addend'.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            new_rel = self.add_right(addend)
        else:
            from . import less_add_left
            new_rel = less_add_left.instantiate(
                    {a: self.lower, b: self.upper, c: addend})
        return new_rel.with_mimicked_style(self)

    @prover
    def add_right(self, addend, **defaults_config):
        '''
        From a < b, derive and return a < b + c given 0 <= c 
        Or from a > b, derive and return a > b + c given c <= 0 
        (and a, b, c are all Real) where c is the given 'addend'.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            new_rel = self.add_left(addend)
        else:
            from . import less_add_right
            new_rel = less_add_right.instantiate(
                {a: self.lower, b: self.upper, c: addend})
        return new_rel.with_mimicked_style(self)
    
    @prover
    def add(self, relation, **defaults_config):
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
                {a: self.lower, b: self.upper, c: _c, d: _d})
        return new_rel.with_mimicked_style(self)

    @prover
    def left_mult_both_sides(self, multiplier, **defaults_config):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers import Less, LessEq, zero, deduce_number_set
        from proveit.numbers.multiplication import (
                strong_bound_via_right_factor_bound,
                weak_bound_via_right_factor_bound,
                reversed_strong_bound_via_right_factor_bound,
                reversed_weak_bound_via_right_factor_bound)
        was_reversed = False
        deduce_number_set(multiplier)
        if Less(zero, multiplier).proven():
            new_rel = strong_bound_via_right_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
        elif Less(multiplier, zero).proven():
            new_rel = reversed_strong_bound_via_right_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
            was_reversed = True
        elif LessEq(zero, multiplier).proven():
            new_rel = weak_bound_via_right_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
        elif LessEq(multiplier, zero).proven():
            new_rel = reversed_weak_bound_via_right_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
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

    @prover
    def right_mult_both_sides(self, multiplier, **defaults_config):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the right.
        '''
        from proveit.numbers import LessEq, zero, deduce_number_set
        from proveit.numbers.multiplication import (
                strong_bound_via_left_factor_bound,
                weak_bound_via_left_factor_bound,
                reversed_strong_bound_via_left_factor_bound,
                reversed_weak_bound_via_left_factor_bound)
        was_reversed = False
        deduce_number_set(multiplier)
        if Less(zero, multiplier).proven():
            new_rel = strong_bound_via_left_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
        elif Less(multiplier, zero).proven():
            new_rel = reversed_strong_bound_via_left_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
            was_reversed = True
        elif LessEq(zero, multiplier).proven():
            new_rel = weak_bound_via_left_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
        elif LessEq(multiplier, zero).proven():
            new_rel = reversed_weak_bound_via_left_factor_bound.instantiate(
                {a: multiplier, x: self.lower, y: self.upper})
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

    @prover
    def divide_both_sides(self, divisor, **defaults_config):
        '''
        Divide both sides of the relation by the 'divisor'.
        '''
        from proveit.numbers import Less, zero, deduce_number_set
        from proveit.numbers.division import (
            strong_div_from_numer_bound__pos_denom, 
            strong_div_from_numer_bound__neg_denom)
        deduce_number_set(divisor)
        if Less(zero, divisor).proven():
            thm = strong_div_from_numer_bound__pos_denom
        elif Less(divisor, zero).proven():
            thm = strong_div_from_numer_bound__neg_denom
        else:
            raise Exception("Cannot divide both sides of %s by %s "
                            "without knowing the divisors "
                            "relation to zero."%(self, divisor))
        new_rel = thm.instantiate(
                {a: divisor, x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    @prover
    def left_add_both_sides(self, addend, **defaults_config):
        '''
        Add to both sides of the relation by the 'addend' on the left.
        '''
        from proveit.numbers.addition import strong_bound_via_right_term_bound
        new_rel = strong_bound_via_right_term_bound.instantiate(
            {a: addend, x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    @prover
    def right_add_both_sides(self, addend, **defaults_config):
        '''
        Add to both sides of the relation by the 'addend' on the right.
        '''
        from proveit.numbers.addition import strong_bound_via_left_term_bound
        new_rel = strong_bound_via_left_term_bound.instantiate(
            {a: addend, x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    @prover
    def exponentiate_both_sides(self, exponent, **defaults_config):
        '''
        Exponentiate both sides of the relation by the 'exponent'.
        '''
        from proveit.numbers import Less, LessEq, zero, deduce_number_set
        from proveit.numbers.exponentiation import (
            exp_pos_less, exp_nonneg_less, exp_neg_less, exp_nonpos_less)
        # We need to know how the exponent relates to zero.
        deduce_number_set(exponent)
        LessEq.sort([zero, exponent])
        if Less(zero, exponent).proven():
            new_rel = exp_pos_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        elif Less(exponent, zero).proven():
            new_rel = exp_neg_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        elif LessEq(zero, exponent).proven():
            new_rel = exp_nonneg_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        elif LessEq(exponent, zero).proven():
            new_rel = exp_nonpos_less.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        else:
            raise Exception("Cannot exponentiate both sides of %s by %s "
                            "without knowing the exponent's relation with "
                            "zero"%(self, exponent))
        return new_rel.with_mimicked_style(self)


def greater(a, b):
    '''
    Return an expression representing a > b, internally represented 
    as b < a but with a style that reverses the direction.    
    '''
    return Less(b, a).with_styles(direction='reversed')
