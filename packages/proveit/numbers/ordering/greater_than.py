from proveit import Literal, USE_DEFAULTS, as_expression
from proveit.logic import Equals
from .ordering_relation import OrderingRelation, OrderingSequence, make_sequence_or_relation
from proveit import a, b, c, d, x, y, z


class GreaterRelation(OrderingRelation):
    def __init__(self, operator, lhs, rhs):
        OrderingRelation.__init__(self, operator, lhs, rhs)

    def lower(self):
        '''
        Returns the lower bound side of this inequality.
        '''
        return self.rhs

    def upper(self):
        '''
        Returns the upper bound side of this inequality.
        '''
        return self.lhs

    @staticmethod
    def WeakRelationClass():
        return GreaterEq  # >= is weaker than >

    @staticmethod
    def StrongRelationClass():
        return Greater  # > is stronger than >=

    @staticmethod
    def SequenceClass():
        return GreaterSequence


class GreaterSequence(OrderingSequence):
    def __init__(self, operators, operands):
        OrderingSequence.__init__(self, operators, operands)
        # Containment in the {>, >=, =} set is relevant when dealing with a GreaterSequence,
        # so let's go ahead and import these unquantified theorems.
        try:
            from . import greater__in__greater_eq_relations, greater_eq__in__greater_eq_relations, eq__in__greater_eq_relations
        except BaseException:
            # may fail before the relevent _theorems_ have been generated
            pass  # and that's okay

    @staticmethod
    def RelationClass():
        return GreaterRelation


class Greater(GreaterRelation):
    # operator of the Greater operation.
    _operator_ = Literal(string_format='>', theory=__file__)

    # map left-hand-sides to ">" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_left_sides = dict()
    # map right-hand-sides to ">" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_right_sides = dict()

    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, Greater._operator_, lhs, rhs)

    def conclude(self, assumptions):
        from . import positive_if_real_pos
        from proveit.numbers import zero
        if self.rhs == zero:
            positive_if_real_pos.instantiate({a: self.lhs},
                                             assumptions=assumptions)
        return GreaterRelation.conclude(self, assumptions)

    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from .less_than import LessThan
        return LessThan(self.rhs, self.lhs)

    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From, x > y derive y < x.
        '''
        from . import reverse_greater
        return reverse_greater.instantiate(
            {x: self.lhs, y: self.rhs}, assumptions=assumptions)

    def deduce_in_bool(self, assumptions=frozenset()):
        from . import greater_than_is_bool
        return greater_than_is_bool.instantiate(
            {x: self.lhs, y: self.rhs}, assumptions=assumptions)

    def derive_relaxed(self, assumptions=frozenset()):
        '''
        Relax a > b to a >= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Real.
        '''
        from . import relax_greater
        return relax_greater.instantiate(
            {x: self.lhs, y: self.rhs}, assumptions=assumptions)

    def deduce_inc_add(self, assumptions=USE_DEFAULTS):
        '''
        created by JML 7/17/19
        if self.lhs is addition, deduce strictly increasing addition
        '''
        from proveit.numbers import Add

        if isinstance(self.lhs, Add):
            return self.lhs.deduce_strict_inc_add(self.rhs, assumptions)
        else:
            raise ValueError("expected self.lhs to be addition")

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        from . import transitivity_greater_greater, transitivity_greater_greater_eq
        from .less_than import Less, LessEq
        other = as_expression(other)
        if isinstance(other, Equals):
            return OrderingRelation.apply_transitivity(
                self, other, assumptions)  # handles this special case
        if isinstance(other, Less) or isinstance(other, LessEq):
            other = other.derive_reversed(assumptions)
        if other.lhs == self.rhs:
            if isinstance(other, Greater):
                return transitivity_greater_greater.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.rhs}, assumptions=assumptions)
            elif isinstance(other, GreaterEq):
                return transitivity_greater_greater_eq.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other, Greater):
                return transitivity_greater_greater.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.lhs}, assumptions=assumptions)
            elif isinstance(other, GreaterEq):
                return transitivity_greater_greater_eq.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.lhs}, assumptions=assumptions)
        else:
            raise ValueError(
                "Cannot perform transitivity with %s and %s!" %
                (self, other))

    def derive_negated(self, assumptions=frozenset()):
        '''
        From :math:`a > b`, derive and return :math:`-a < -b`.
        Assumptions may be required to prove that a, and b are in Real.
        '''
        from . import negated_greater_than
        return negated_greater_than.instantiate({a: self.lhs, b: self.rhs})

    def derive_shifted(
            self,
            addend,
            addend_side='right',
            assumptions=USE_DEFAULTS):
        r'''
        From a > b, derive and return a + c > b + c
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in
        Real.
        '''
        from . import greater_shift_add_right, greater_shift_add_left
        if addend_side == 'right':
            return greater_shift_add_right.instantiate(
                {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)
        elif addend_side == 'left':
            return greater_shift_add_left.instantiate(
                {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)
        else:
            raise ValueError(
                "Unrecognized addend side (should be 'left' or 'right'): " +
                str(addend_side))

    def add_left(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a > b, derive and return a + c > b given c >= 0 (and a, b, c
        are all Real) where c is the given 'addend'.
        '''
        from . import greater_add_left
        return greater_add_left.instantiate(
            {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)

    def add_right(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a > b, derive and return a > b + c given 0 >= c (and a, b, c
        are all Real) where c is the given 'addend'.
        '''
        from . import greater_add_right
        return greater_add_right.instantiate(
            {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)

    def add(self, relation, assumptions=USE_DEFAULTS):
        '''
        From a > b, derive and return a + c > b + d given c > d
        (and a, b, c, d are all Real).  c and d are determined from the
        given 'relation'.
        '''
        from .less_than import Less, LessEq
        from . import greater_add_both
        if isinstance(relation, Greater) or isinstance(relation, GreaterEq):
            c_val = relation.lhs
            d_val = relation.rhs
        elif isinstance(relation, Less) or isinstance(relation, LessEq):
            c_val = relation.rhs
            d_val = relation.lhs
        else:
            raise ValueError("Greater.add 'relation' must be of type Less, "
                             "LessEq, Greater, or GreaterEq, not %s"
                             % str(relation.__class__))
        return greater_add_both.instantiate({a: self.lhs, b: self.rhs, c: c_val,
                                             d: d_val},
                                            assumptions=assumptions)

    def conclude_via_equality(self, assumptions=USE_DEFAULTS):
        from . import relax_equal_to_greater_eq
        return relax_equal_to_greater_eq.instantiate(
            {x: self.operands[0], y: self.operands[1]},
            assumptions=assumptions)


class GreaterEq(GreaterRelation):
    # operator of the GreaterEq operation.
    _operator_ = Literal(
        string_format='>=',
        latex_format=r'\geq',
        theory=__file__)

    # map left-hand-sides to ">=" Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to ">=" Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        GreaterRelation.__init__(self, GreaterEq._operator_, lhs, rhs)

    def conclude(self, assumptions):
        # See if the right side is the left side plus something
        # positive added to it.
        from proveit.numbers import zero
        if self.rhs == zero:
            from . import non_neg_if_real_non_neg
            return non_neg_if_real_non_neg.instantiate(
                {a: self.lhs}, assumptions=assumptions)
        return GreaterRelation.conclude(self, assumptions)

    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from .less_than import LessThanEquals
        return LessThanEquals(self.rhs, self.lhs)

    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From, x >= y derive y <= x.
        '''
        from . import reverse_greater_eq
        return reverse_greater_eq.instantiate(
            {x: self.lhs, y: self.rhs}, assumptions=assumptions)

    def deduce_in_bool(self, assumptions=frozenset()):
        from . import greater_than_equals_is_bool
        return greater_than_equals_is_bool.instantiate(
            {x: self.lhs, y: self.rhs}, assumptions=assumptions)

    def unfold(self, assumptions=frozenset()):
        from . import greater_than_equals_def
        return greater_than_equals_def.instantiate({x: self.lhs, y: self.rhs})

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this x>=y expression
        and something of the form y>z, y>=z, z<y, z<=y, or y=z to
        obtain x>z or x>=z as appropriate.  In the special case
        of x>=y and y>=x (or x<=y), derive x=z.
        '''
        from . import transitivity_greater_eq_greater, transitivity_greater_eq_greater_eq, symmetric_greater_eq
        from .less_than import Less, LessEq
        other = as_expression(other)
        if isinstance(other, Equals):
            return OrderingRelation.apply_transitivity(
                self, other, assumptions)  # handles this special case
        if isinstance(other, Less) or isinstance(other, LessEq):
            other = other.derive_reversed(assumptions)
        if other.lhs == self.rhs and other.rhs == self.lhs:
            # x >= y and y >= x implies that x=y
            return symmetric_greater_eq.instantiate(
                {x: self.lhs, y: self.rhs}, assumptions=assumptions)
        elif other.lhs == self.rhs:
            if isinstance(other, Greater):
                return transitivity_greater_eq_greater.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.rhs}, assumptions=assumptions)
            elif isinstance(other, GreaterEq):
                return transitivity_greater_eq_greater_eq.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other, Greater):
                return transitivity_greater_eq_greater.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.lhs}, assumptions=assumptions)
            elif isinstance(other, GreaterEq):
                return transitivity_greater_eq_greater_eq.instantiate(
                    {x: self.lhs, y: self.rhs, z: other.lhs}, assumptions=assumptions)
        else:
            raise ValueError(
                "Cannot perform transitivity with %s and %s!" %
                (self, other))

    """
    def derive_negated(self, assumptions=frozenset()):
        '''
        From :math:`a \geq b`, derive and return :math:`-a \leq -b`.
        Assumptions may be required to prove that a, and b are in Real.
        '''
        from . import negated_greater_than_equals
        return negated_greater_than_equals.instantiate({a:self.lhs, b:self.rhs})
    """

    def derive_shifted(
            self,
            addend,
            addend_side='right',
            assumptions=USE_DEFAULTS):
        r'''
        From a >= b, derive and return a + c >= b + c
        where c is the given 'addend'.
        Assumptions may be required to prove that a, b, and c are in
        Real.
        '''
        from . import greater_eq_shift_add_right, greater_eq_shift_add_left
        if addend_side == 'right':
            return greater_eq_shift_add_right.instantiate(
                {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)
        elif addend_side == 'left':
            return greater_eq_shift_add_left.instantiate(
                {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)
        else:
            raise ValueError(
                "Unrecognized addend side (should be 'left' or 'right'): " +
                str(addend_side))

    def add_left(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a >= b, derive and return a + c >= b given c >= 0 (and a, b, c
        are all Real) where c is the given 'addend'.
        '''
        from . import greater_eq_add_left
        return greater_eq_add_left.instantiate(
            {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)

    def add_right(self, addend, assumptions=USE_DEFAULTS):
        '''
        From a >= b, derive and return a >= b + c given 0 >= c (and a, b, c
        are all Real) where c is the given 'addend'.
        '''
        from . import greater_eq_add_right
        return greater_eq_add_right.instantiate(
            {a: self.lhs, b: self.rhs, c: addend}, assumptions=assumptions)

    def add(self, relation, assumptions=USE_DEFAULTS):
        '''
        From a >= b, derive and return a + c >= b + d given c >= d
        (and a, b, c, d are all Real).  c and d are determined from the
        given 'relation'.
        '''
        from .less_than import Less, LessEq
        from . import greater_eq_add_both
        if isinstance(relation, Greater) or isinstance(relation, GreaterEq):
            c_val = relation.lhs
            d_val = relation.rhs
        elif isinstance(relation, Less) or isinstance(relation, LessEq):
            c_val = relation.rhs
            d_val = relation.lhs
        else:
            raise ValueError("Greater.add 'relation' must be of type Less, "
                             "LessEq, Greater, or GreaterEq, not %s"
                             % str(relation.__class__))
        return greater_eq_add_both.instantiate({a: self.lhs, b: self.rhs, c: c_val,
                                                d: d_val},
                                               assumptions=assumptions)


def GreaterOnlySeq(*operands):
    return GreaterSequence([Greater._operator_] *
                           (len(operands) - 1), operands)


def GreaterEqOnlySeq(*operands):
    return GreaterSequence([GreaterEq._operator_] *
                           (len(operands) - 1), operands)


def greater_sequence(operators, operands):
    '''
    Create a GreaterSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    return make_sequence_or_relation(GreaterSequence, operators, operands)
