from proveit import (Literal, Operation, USE_DEFAULTS, as_expression,
                     UnsatisfiedPrerequisites, prover, relation_prover)
from proveit.logic import Equals
from proveit.util import OrderedSet
from proveit import a, b, c, d, x, y, z
from .number_ordering_relation import NumberOrderingRelation

class LessEq(NumberOrderingRelation):
    # operator of the LessEq operation.
    _operator_ = Literal(
        string_format='<=',
        latex_format=r'\leq',
        theory=__file__)

    # map left-hand-sides to "<=" Judgments
    #   (populated in TransitivityRelation._record_as_proven)
    known_left_sides = dict()
    # map right-hand-sides to "<=" Judgments
    #   (populated in TransitivityRelation._record_as_proven)
    known_right_sides = dict()

    # map canonical left hand sides to '<' Judgments paired with
    # canonical left hand sides.
    known_canonical_bounds = dict()

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

    def _record_as_proven(self, judgment):
        '''
        Remember the canonical bound of this proven LessEq.
        '''
        NumberOrderingRelation._record_as_proven(self, judgment)
        canonical_form = self.canonical_form()
        known_canonical_bounds = LessEq.known_canonical_bounds
        known_canonical_bounds.setdefault(
                canonical_form.lhs, OrderedSet()).add(
                (judgment, canonical_form.rhs))
        
    def side_effects(self, judgment):
        '''
        In addition to the NumberOrderingRelation side-effects, also
        derive a ≠ b from a < b as a side-effect.
        '''
        for side_effect in NumberOrderingRelation.side_effects(
                self, judgment):
            yield side_effect
        yield self.derive_complement
        # if is_numeric_int(self.lhs) or is_numeric_int(self.rhs):
        #     yield self.derive_one_side_in_real_subset

    def negation_side_effects(self, judgment):
        '''
        From Not(a <= b) derive a > b as a side-effect.
        '''
        yield self.deduce_complement_of_complement

    @prover
    def conclude(self, **defaults_config):
        '''
        Conclude something of the form 
        a ≤ b.
        '''
        from proveit.numbers import (Add, Real, RealNonNeg, RealNonPos, 
                                     readily_provable_number_set,
                                     deduce_number_set)
        if Equals(self.lower, self.upper).readily_provable():
            # We can prove that a = b, therefore a ≤ b.
            return self.conclude_via_equality()

        lower, upper = self.lower, self.upper
        lower_ns = readily_provable_number_set(
                lower, _check_order_against_zero=False, default=Real)
        upper_ns = readily_provable_number_set(
                upper, _check_order_against_zero=False, default=Real)
        if RealNonPos.readily_includes(lower_ns) and (
                RealNonNeg.readily_includes(upper_ns)):
            # The inequality is determined by the number sets.
            deduce_number_set(lower)
            deduce_number_set(upper)

        try:
            # If there is a known bound that is similar and at least
            # as strong, we can derive this bound from the known one.
            return self.conclude_from_known_bound()
        except UnsatisfiedPrerequisites:
            pass

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
    def conclude_via_equality(self, **defaults_config):
        '''
        Conclude a ≤ b from a = b.
        '''
        from . import relax_equal_to_less_eq
        return relax_equal_to_less_eq.instantiate(
            {x: self.operands[0], y: self.operands[1]})

    @prover
    def conclude_as_bounded_by_term(self, **defaults_config):
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
            return self.lower.bound_by_term(self.upper, use_weak_bound=True)
        elif (isinstance(self.upper, Add) and 
                self.lower in self.upper.terms.entries):
            return self.upper.bound_by_term(self.lower, use_weak_bound=True)
        else:
            raise ValueError("LessEq.conclude_as_bounded_by_term is only "
                             "applicable if one side of the Less "
                             "expression is an addition and the other "
                             "side is one of the terms")

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Automatically conclude the negation an OrderingRelation.
        For example, not(7 ≤ 3) from 3 < 7.
        '''
        from .less import Less
        return Less(self.upper, self.lower).derive_complement()

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import less_than_equals_is_bool
        is_bool_stmt = less_than_equals_is_bool.instantiate(
            {x: self.lower, y: self.upper})
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

    @prover
    def unfold(self, **defaults_config):
        from . import less_eq_def
        unfolded = less_eq_def.instantiate({x: self.lower, y: self.upper})
        return unfolded.inner_expr().operands[0].with_mimicked_style(self)
    
    @prover
    def apply_transitivity(self, other, **defaults_config):
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
                self, other)  # handles this special case
        if other.lower == self.upper and other.upper == self.lower:
            # x <= y and y <= x implies that x=y
            return symmetric_less_eq.instantiate(
                {x: self.lower, y: self.upper})
        elif other.lower == self.upper:
            if isinstance(other, Less):
                new_rel = transitivity_less_eq_less.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper},
                    preserve_all=True)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_eq_less_eq.instantiate(
                    {x: self.lower, y: self.upper, z: other.upper},
                    preserve_all=True)
        elif other.upper == self.lower:
            if isinstance(other, Less):
                new_rel = transitivity_less_less_eq.instantiate(
                    {x: other.lower, y: other.upper, z: self.upper},
                    preserve_all=True)
            elif isinstance(other, LessEq):
                new_rel = transitivity_less_eq_less_eq.instantiate(
                    {x: other.lower, y: other.upper, z: self.upper},
                    preserve_all=True)
        else:
            raise ValueError(
                "Cannot perform transitivity with %s and %s!" %
                (self, other))
        return new_rel.with_mimicked_style(self)

    @prover
    def derive_negated(self, **defaults_config):
        '''
        From a <= b, derive and return -b <= -a.
        '''
        from proveit.numbers.negation import negated_weak_bound
        new_rel = negated_weak_bound.instantiate(
                {x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    # Temporarily leaving the original here while testing continues.
    # @prover
    # def deduce_complement(self, **defaults_config):
    #     '''
    #     From Not(a <= b), derive and return (b < a).
    #     '''
    #     from . import less_eq_complement_is_greater
    #     return less_eq_complement_is_greater.instantiate(
    #             {x:self.lower, y:self.upper}).derive_consequent()

    @prover
    def derive_complement(self, **defaults_config):
        '''
        From (a <= b), derive and return Not(b < a).
        '''
        from . import not_less_from_less_eq
        return not_less_from_less_eq.instantiate(
                {x: self.lower, y: self.upper})

    @prover
    def deduce_complement_of_complement(self, **defaults_config):
        '''
        From Not(a <= b), derive and return (b < a);
        and from (a <= b), derive and return Not(b < a).
        '''
        from . import less_from_not_less_eq
        return less_from_not_less_eq.instantiate(
                {x: self.lower, y: self.upper})

    @prover
    def shallow_simplification_of_negation(self, **defaults_config):
        '''
        Prove and return Not(a <= b) = (b < a) as a simplification.
        '''
        from . import less_eq_complement_is_greater
        return less_eq_complement_is_greater.instantiate(
                {x:self.lower, y:self.upper})

    @prover
    def derive_shifted(self, addend, addend_side='right',
            **defaults_config):
        r'''
        From a <= b, derive and return a + c <= b + c
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in
        Real.
        '''
        from . import less_eq_shift_add_right, less_eq_shift_add_left  # , less_than_subtract
        if addend_side == 'right':
            new_rel = less_eq_shift_add_right.instantiate(
                {a: self.lower, b: self.upper, c: addend})
        elif addend_side == 'left':
            new_rel = less_eq_shift_add_left.instantiate(
                {a: self.lower, b: self.upper, c: addend})
        else:
            raise ValueError(
                "Unrecognized addend side (should be 'left' or 'right'): " +
                str(addend_side))
        return new_rel.with_mimicked_style(self)
    
    @prover
    def add_left(self, addend, *, strong=False,
                 **defaults_config):
        '''
        From a <= b, derive and return a + c <= b given c <= 0 
        Or from a >= b, derive and return a + c >= b given 0 <= c 
        (and a, b, c are all Real) where c is the given 'addend'.

        If 'strong' is True, we derive the strong < (>) form and
        c must be provably non-zero.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            temp_rel = self.with_styles(direction='normal')
            new_rel = temp_rel.add_right(addend, strong=strong)
        else:
            from . import less_eq_add_left, less_eq_add_left_strong
            if strong:
                new_rel = less_eq_add_left_strong.instantiate(
                    {a: self.lower, b: self.upper, c: addend})
            else:
                new_rel = less_eq_add_left.instantiate(
                    {a: self.lower, b: self.upper, c: addend})
        return new_rel.with_mimicked_style(self)

    @prover
    def add_right(self, addend, *, strong=False, **defaults_config):
        '''
        From a <= b, derive and return a <= b + c given 0 <= c 
        Or from a >= b, derive and return a >= b + c given c <= 0 
        (and a, b, c are all Real) where c is the given 'addend'.

        If 'strong' is True, we derive the strong < (>) form and
        c must be provably non-zero.
        '''
        if self.get_style('direction', 'normal') == 'reversed':
            # Left and right are reversed.
            temp_rel = self.with_styles(direction='normal')
            new_rel = temp_rel.add_left(addend, strong=strong)
        else:
            from . import less_eq_add_right, less_eq_add_right_strong
            if strong:
                new_rel = less_eq_add_right_strong.instantiate(
                    {a: self.lower, b: self.upper, c: addend})
            else:
                new_rel = less_eq_add_right.instantiate(
                    {a: self.lower, b: self.upper, c: addend})
        return new_rel.with_mimicked_style(self)

    @prover
    def add(self, relation, **defaults_config):
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
                {a: self.lower, b: self.upper, c: _c, d: _d})
        return new_rel.with_mimicked_style(self)
    
    @prover
    def left_mult_both_sides(self, multiplier, **defaults_config):
        '''
        Multiply both sides of the relation by the 'multiplier'
        on the left.
        '''
        from proveit.numbers import greater_eq, zero, deduce_number_set
        from proveit.numbers.multiplication import (
            weak_bound_via_right_factor_bound,
            reversed_weak_bound_via_right_factor_bound)
        was_reversed = False
        deduce_number_set(multiplier)
        if greater_eq(multiplier, zero).proven():
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
        from proveit.numbers import zero, deduce_number_set
        from proveit.numbers.multiplication import (
            weak_bound_via_left_factor_bound,
            reversed_weak_bound_via_left_factor_bound)
        was_reversed = False
        deduce_number_set(multiplier)
        if LessEq(zero, multiplier).proven():
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
            weak_div_from_numer_bound__pos_denom, 
            weak_div_from_numer_bound__neg_denom)
        deduce_number_set(divisor)
        if Less(zero, divisor).proven():
            thm = weak_div_from_numer_bound__pos_denom
        elif Less(divisor, zero).proven():
            thm = weak_div_from_numer_bound__neg_denom
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
        from proveit.numbers.addition import weak_bound_via_right_term_bound
        new_rel = weak_bound_via_right_term_bound.instantiate(
            {a: addend, x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    @prover
    def right_add_both_sides(self, addend, **defaults_config):
        '''
        Add to both sides of the relation by the 'addend' on the right.
        '''
        from proveit.numbers.addition import weak_bound_via_left_term_bound
        new_rel = weak_bound_via_left_term_bound.instantiate(
            {a: addend, x: self.lower, y: self.upper})
        return new_rel.with_mimicked_style(self)

    @prover
    def exponentiate_both_sides(self, exponent, **defaults_config):
        '''
        Exponentiate both sides of the relation by the 'exponent'.
        '''
        from proveit.numbers import Less, zero, deduce_number_set
        from proveit.numbers.exponentiation import (
            exp_pos_lesseq, exp_nonneg_lesseq,
            exp_neg_lesseq, exp_nonpos_lesseq)
        # We need to know how the exponent relates to zero.
        deduce_number_set(exponent)
        LessEq.sort([zero, exponent])
        if Less(zero, exponent).proven():
            new_rel = exp_pos_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        elif Less(exponent, zero).proven():
            new_rel = exp_neg_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        elif LessEq(zero, exponent).proven():
            new_rel = exp_nonneg_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        elif LessEq(exponent, zero).proven():
            new_rel = exp_nonpos_lesseq.instantiate(
                {a: exponent, x: self.lower, y: self.upper})
        else:
            raise Exception("Cannot exponentiate both sides of %s by %s "
                            "without knowing the exponent's relation with "
                            "zero"%(self, exponent))
        return new_rel.with_mimicked_style(self)

    @prover
    def derive_one_side_in_real_subset(self, **defaults_config):
        # FINISH THIS UP
        # check for one side or the other equal to some literal number
        # go for RealPos, RealNeg, RealNonNeg, etc
        # using conclude_via_transitivity
        # actually can put this one level up in the number_ordering_relation
        pass


def greater_eq(a, b):
    '''
    Return an expression representing a >= b, internally represented 
    as b <= a but with a style that reverses the direction.    
    '''
    return LessEq(b, a).with_styles(direction='reversed')
