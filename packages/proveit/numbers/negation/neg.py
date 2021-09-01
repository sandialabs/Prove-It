from proveit import (Expression, Literal, Operation, maybe_fenced_string, 
                     maybe_fenced_latex, InnerExpr, defaults, USE_DEFAULTS, 
                     ProofFailure, relation_prover, equality_prover)
from proveit.logic import is_irreducible_value
from proveit.numbers.number_sets import (
        Natural, NaturalPos, 
        Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
        Rational, RationalNonZero, RationalPos, RationalNeg,
        RationalNonNeg, RationalNonPos,
        Real, RealNonZero, RealPos, RealNeg, RealNonNeg, RealNonPos,
        Complex, ComplexNonZero)
from proveit import a, b, c, m, n, x, y, B
from proveit.numbers import NumberOperation

class Neg(NumberOperation):
    # operator of the Neg operation.
    _operator_ = Literal(string_format='-', theory=__file__)

    def __init__(self, A, *, styles=None):
        NumberOperation.__init__(self, Neg._operator_, A, styles=styles)

    def is_irreducible_value(self):
        from proveit.numbers import zero
        if isinstance(self.operand, Neg):
            return False # double negation is reducible
        return is_irreducible_value(self.operand) and self.operand != zero

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        given a number set, attempt to prove that the given expression
        is in that number set using the appropriate closure theorem
        '''
        from . import (nat_closure, nat_pos_closure, 
                       int_closure, int_nonzero_closure, 
                       int_neg_closure, int_nonpos_closure,
                       rational_closure, rational_nonzero_closure,
                       rational_pos_closure, rational_neg_closure,
                       rational_nonneg_closure, rational_nonpos_closure,
                       real_closure, real_nonzero_closure, 
                       real_pos_closure, real_neg_closure,
                       real_nonneg_closure, real_nonpos_closure, 
                       complex_closure, complex_nonzero_closure)
        if number_set == Natural:
            return nat_closure.instantiate({a: self.operand})
        elif number_set == NaturalPos:
            return nat_pos_closure.instantiate({a: self.operand})
        elif number_set == Integer:
            return int_closure.instantiate({a: self.operand})
        elif number_set == IntegerNonZero:
            return int_nonzero_closure.instantiate({a: self.operand})
        elif number_set == IntegerNeg:
            return int_neg_closure.instantiate({a: self.operand})
        elif number_set == IntegerNonPos:
            return int_nonpos_closure.instantiate({a: self.operand})
        elif number_set == Rational:
            return rational_closure.instantiate({a: self.operand})
        elif number_set == RationalNonZero:
            return rational_nonzero_closure.instantiate({a: self.operand})
        elif number_set == RationalPos:
            return rational_pos_closure.instantiate({a: self.operand})
        elif number_set == RationalNeg:
            return rational_neg_closure.instantiate({a: self.operand})
        elif number_set == RationalNonNeg:
            return rational_nonneg_closure.instantiate({a: self.operand})
        elif number_set == RationalNonPos:
            return rational_nonpos_closure.instantiate({a: self.operand})
        elif number_set == Real:
            return real_closure.instantiate({a: self.operand})
        elif number_set == RealNonZero:
            return real_nonzero_closure.instantiate({a: self.operand})
        elif number_set == RealPos:
            return real_pos_closure.instantiate({a: self.operand})
        elif number_set == RealNeg:
            return real_neg_closure.instantiate({a: self.operand})
        elif number_set == RealNonNeg:
            return real_nonneg_closure.instantiate({a: self.operand})
        elif number_set == RealNonPos:
            return real_nonpos_closure.instantiate({a: self.operand})
        elif number_set == Complex:
            return complex_closure.instantiate({a: self.operand})
        elif number_set == ComplexNonZero:
            return complex_nonzero_closure.instantiate({a: self.operand})
        raise NotImplementedError(
            "No negation closure theorem for set %s" %str(number_set))

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Neg
        expression assuming the operands have been simplified.
        
        Handle negation of 0 and double negation specifically.
        '''
        from proveit.logic import EvaluationError
        from . import negated_zero
        from proveit.numbers import zero
        
        if must_evaluate and not is_irreducible_value(self.operand):
            # The simplification of the operands may not have
            # worked hard enough.  Let's work harder if we
            # must evaluate.
            self.operand.evalution()
            return self.evaluation()
        
        if self.operand == zero:
            return negated_zero
        # Handle double negation:
        if isinstance(self.operand, Neg):
            # simplify double negation
            return self.double_neg_simplification()
        return Expression.shallow_simplification(self)

    @equality_prover('double_neg_simplified', 'double_neg_simplify')
    def double_neg_simplification(self, **defaults_config):
        from . import double_negation
        assert isinstance(
            self.operand, Neg), "Expecting a double negation: %s" % str(self)
        return double_negation.instantiate({x: self.operand.operand})

    """
    def _closureTheorem(self, number_set):
        import _theorems_
        if number_set == Complex:
            return _theorems_.neg_complex_closure
        elif number_set == Real:
            return _theorems_.neg_real_closure
        elif number_set == Integer:
            return _theorems_.neg_int_closure

    def _negativeTheorem(self):
        import _theorems_
        return _theorems_.negated_positive_is_negative

    def _positiveTheorem(self):
        import _theorems_
        return _theorems_.negated_negative_is_positive

    def _not_eqZeroTheorem(self):
        import _theorems_
        return _theorems_.neg_not_eq_zero
    """

    def as_int(self):
        '''
        Convert a literal integer into a Python int.  This
        only works if the operand is a literal int.
        '''
        return -self.operand.as_int()

    def string(self, **kwargs):
        return maybe_fenced_string(
            '-' +
            self.operand.string(
                fence=True),
            **kwargs)

    def latex(self, **kwargs):
        return maybe_fenced_latex(
            '-' +
            self.operand.latex(
                fence=True),
            **kwargs)

    @equality_prover('distributed', 'distribute')
    def distribution(self, **defaults_config):
        '''
        Distribute negation through a sum (Add) or over a fraction
        (Div), deducing and returning the equality between the
        original and distributed forms.
        '''
        from . import distribute_neg_through_binary_sum
        from . import (
                distribute_neg_through_subtract, distribute_neg_through_sum)
        from . import distribute_neg_through_div_numerator
        from proveit.numbers import Add, Div

        if isinstance(self.operand, Add):
            # Distribute negation through a sum.
            add_expr = self.operand
            if add_expr.operands.is_double():
                # special case of 2 operands
                if isinstance(add_expr.operands[1], Neg):
                    return distribute_neg_through_subtract.instantiate(
                        {a: add_expr.operands[0],
                         b: add_expr.operands[1].operand})
                else:
                    return distribute_neg_through_binary_sum.instantiate(
                        {a: add_expr.operands[0], b: add_expr.operands[1]})
            else:
                # distribute the negation over the sum
                _x = add_expr.operands
                _n = _x.num_elements()
                return distribute_neg_through_sum.instantiate(
                        {n: _n, x: _x})
        elif isinstance(self.operand, Div):
            # distribute the negation over the fraction
            _x_sub = self.operand.numerator
            _y_sub = self.operand.denominator
            return distribute_neg_through_div_numerator.instantiate(
                    {x: _x_sub, y: _y_sub})
        else:
            raise Exception(
                "Only negation distribution through a sum, subtract, or "
                "fraction (Div) is implemented.")

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factor, pull="left", group_factor=None,
                      group_remainder=None, **defaults_config):
        '''
        Pull out a factor from a negated expression, pulling it either
        to the "left" or "right".  group_factor and group_remainder are 
        not relevant but kept for compatibility with other factor 
        methods.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are 
        in the Complex numbers so that the associative and commutation 
        theorems are applicable.
        FACTORING FROM NEGATION FROM A SUM NOT IMPLEMENTED YET.
        '''
        from . import (neg_times_pos, pos_times_neg, mult_neg_one_left,
                       mult_neg_one_right)
        if isinstance(the_factor, Neg):
            if pull == 'left':
                thm = neg_times_pos
            else:
                thm = pos_times_neg
            the_factor = the_factor.operand
        else:
            if pull == 'left':
                thm = pos_times_neg
            else:
                thm = neg_times_pos
        if hasattr(self.operand, 'factorization'):
            operand_factor_eqn = self.operand.factorization(
                the_factor, pull, group_factor=True, group_remainder=True,
                preserve_all=True)
            eqn1 = operand_factor_eqn.substitution(self.inner_expr().operand)
            new_operand = operand_factor_eqn.rhs
            eqn2 = thm.instantiate(
                {x: new_operand.operands[0], y: new_operand.operands[1]},
                auto_simplify=False, preserve_expr=eqn1.rhs
                ).derive_reversed()
            return eqn1.apply_transitivity(eqn2)
        else:
            if self.operand != the_factor:
                raise ValueError("%s is not a factor in %s!" % (the_factor, self))
            if thm == neg_times_pos:
                thm = mult_neg_one_left
            if thm == pos_times_neg:
                thm = mult_neg_one_right
            return thm.instantiate(
                {x: self.operand}, auto_simplify=False).derive_reversed()

    @equality_prover('inner_neg_mult_simplified',
                        'inner_neg_mult_simplify')
    def inner_neg_mult_simplification(self, idx, **defaults_config):
        '''
        Equivalence method to derive a simplification when negating
        a multiplication with a negated factor.  For example,
        -(a*b*(-c)*d) = a*b*c*d.
        See Mult.neg_simplification where this may be used indirectly.
        '''
        from proveit.numbers import Mult
        from . import mult_neg_left_double, mult_neg_right_double, mult_neg_any_double

        mult_expr = self.operand
        if not isinstance(mult_expr, Mult):
            raise ValueError(
                "Operand expected to be a Mult expression for %s" %
                (idx, str(self)))
        if not isinstance(mult_expr.operands[idx], Neg):
            raise ValueError(
                "Operand at the index %d expected to be a negation for %s" %
                (idx, str(mult_expr)))

        if mult_expr.operands.is_double():
            if idx == 0:
                return mult_neg_left_double.instantiate(
                    {a: mult_expr.operands[1]})
            else:
                return mult_neg_right_double.instantiate(
                    {a: mult_expr.operands[0]})
        _a = mult_expr.operands[:idx]
        _b = mult_expr.operands[idx]
        _c = mult_expr.operands[idx + 1:]
        _m = _a.num_elements()
        _n = _c.num_elements()
        return mult_neg_any_double.instantiate(
            {m: _m, n: _n, a: _a, b: _b, c: _c})
