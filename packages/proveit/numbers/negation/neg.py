from proveit import (Literal, Operation, maybe_fenced_string, 
                     maybe_fenced_latex, InnerExpr, defaults, USE_DEFAULTS, 
                     ProofFailure, equivalence_prover)
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

    def irreducible_value(self):
        from proveit.numbers import zero
        return is_irreducible_value(self.operand) and self.operand != zero

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        given a number set, attempt to prove that the given expression is in that
        number set using the appropriate closure theorem
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
        from proveit.logic import InSet
        if number_set == Natural:
            return nat_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == NaturalPos:
            return nat_pos_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == Integer:
            return int_closure.instantiate(
                    {a: self.operand},  assumptions=assumptions)
        elif number_set == IntegerNonZero:
            return int_nonzero_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == IntegerNeg:
            return int_neg_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == IntegerNonPos:
            return int_nonpos_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == Rational:
            return rational_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RationalNonZero:
            return rational_nonzero_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RationalPos:
            return rational_pos_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RationalNeg:
            return rational_neg_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RationalNonNeg:
            return rational_nonneg_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RationalNonPos:
            return rational_nonpos_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == Real:
            return real_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RealNonZero:
            return real_nonzero_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RealPos:
            return real_pos_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RealNeg:
            return real_neg_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RealNonNeg:
            return real_nonneg_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == RealNonPos:
            return real_nonpos_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == Complex:
            return complex_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        elif number_set == ComplexNonZero:
            return complex_nonzero_closure.instantiate(
                    {a: self.operand}, assumptions=assumptions)
        raise NotImplementedError(
            "No negation closure theorem for set %s" %str(number_set))

    @equivalence_prover('shallow_evaluated', 'shallow_evaluate')
    def shallow_evaluation(self, **defaults_config):
        '''
        Returns a proven evaluation equation for this Neg
        expression assuming the operands have been simplified or
        raises an EvaluationError or ProofFailure (e.g., if appropriate
        number set membership has not been proven).
        
        Handles -0 = 0 or double negation.
        '''
        from proveit.logic import EvaluationError
        from . import negated_zero
        from proveit.numbers import zero
        if self.operand == zero:
            return negated_zero
        if isinstance(self.operand, Neg) and is_irreducible_value(
                self.operand.operand):
            return self.double_neg_simplification()
        raise EvaluationError(self)

    @equivalence_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, **defaults_config):
        '''
        Returns a proven simplification equation for this Neg
        expression assuming the operands have been simplified.
        
        Handles double negation specifically.
        '''
        from proveit.relation import TransRelUpdater

        expr = self
        # For convenience updating our equation:
        eq = TransRelUpdater(expr)
        # Handle double negation:
        if isinstance(self.operand, Neg):
            # simplify double negation
            expr = eq.update(self.double_neg_simplification())
            # simplify what is inside the double-negation.
            expr = eq.update(expr.simplification())
        return eq.relation

    def double_neg_simplification(self, assumptions=USE_DEFAULTS):
        from . import double_negation
        assert isinstance(
            self.operand, Neg), "Expecting a double negation: %s" % str(self)
        return double_negation.instantiate({x: self.operand.operand},
                                           assumptions=assumptions)

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

    def distribution(self, assumptions=USE_DEFAULTS):
        '''
        Distribute negation through a sum, deducing and returning
        the equality between the original and distributed forms.
        '''
        from . import distribute_neg_through_binary_sum
        from . import distribute_neg_through_subtract, distribute_neg_through_sum
        from proveit.numbers import Add
        from proveit.relation import TransRelUpdater
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr, assumptions)

        if isinstance(self.operand, Add):
            # Distribute negation through a sum.
            add_expr = self.operand
            if add_expr.operands.is_double():
                # special case of 2 operands
                if isinstance(add_expr.operands[1], Neg):
                    expr = eq.update(distribute_neg_through_subtract.instantiate(
                        {a: add_expr.operands[0], b: add_expr.operands[1].operand}, assumptions=assumptions))
                else:
                    expr = eq.update(distribute_neg_through_binary_sum.instantiate(
                        {a: add_expr.operands[0], b: add_expr.operands[1]}, assumptions=assumptions))
            else:
                # distribute the negation over the sum
                _x = add_expr.operands
                _n = _x.num_elements(assumptions)
                expr = eq.update(distribute_neg_through_sum.instantiate(
                    {n: _n, x: _x}), assumptions=assumptions)
            assert isinstance(
                expr, Add), "distribute_neg theorems are expected to yield an Add expression"
            # check for double negation
            for k, operand in enumerate(expr.operands):
                assert isinstance(
                    operand, Neg), "Each term from distribute_neg_through_sum is expected to be negated"
                if isinstance(operand.operand, Neg):
                    expr = eq.update(
                        expr.inner_expr().operands[k].double_neg_simplification())
            return eq.relation
        else:
            raise Exception(
                'Only negation distribution through a sum or subtract is implemented')

    def factorization(
            self,
            the_factor,
            pull="left",
            group_factor=None,
            group_remainder=None,
            assumptions=USE_DEFAULTS):
        '''
        Pull out a factor from a negated expression, pulling it either to the "left" or "right".
        group_factor and group_remainder are not relevant but kept for compatibility with
        other factor methods.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in the Complex numbers so that
        the associative and commutation theorems are applicable.
        FACTORING FROM NEGATION FROM A SUM NOT IMPLEMENTED YET.
        '''
        from . import neg_times_pos, pos_times_neg, mult_neg_one_left, mult_neg_one_right
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
                the_factor,
                pull,
                group_factor=True,
                group_remainder=True,
                assumptions=assumptions)
            eqn1 = operand_factor_eqn.substitution(self.inner_expr().operand)
            new_operand = operand_factor_eqn.rhs
            eqn2 = thm.instantiate(
                {
                    x: new_operand.operands[0],
                    y: new_operand.operands[1]},
                assumptions=assumptions).derive_reversed(assumptions)
            return eqn1.apply_transitivity(eqn2, assumptions=assumptions)
        else:
            if self.operand != the_factor:
                raise ValueError("%s is not a factor in %s!" % (the_factor, self))
            if thm == neg_times_pos:
                thm = mult_neg_one_left
            if thm == pos_times_neg:
                thm = mult_neg_one_right
            return thm.instantiate(
                {x: self.operand}, assumptions=assumptions).derive_reversed(assumptions)

    def inner_neg_mult_simplification(self, idx, assumptions=USE_DEFAULTS):
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
                    {a: mult_expr.operands[1]}, assumptions=assumptions)
            else:
                return mult_neg_right_double.instantiate(
                    {a: mult_expr.operands[0]}, assumptions=assumptions)
        _a = mult_expr.operands[:idx]
        _b = mult_expr.operands[idx]
        _c = mult_expr.operands[idx + 1:]
        _m = _a.num_elements(assumptions)
        _n = _c.num_elements(assumptions)
        return mult_neg_any_double.instantiate(
            {m: _m, n: _n, a: _a, b: _b, c: _c}, assumptions=assumptions)


# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(
    Neg,
    'double_neg_simplification',
    'double_neg_simplified',
    'double_neg_simplify')
InnerExpr.register_equivalence_method(
    Neg, 'distribution', 'distributed', 'distribute')
InnerExpr.register_equivalence_method(
    Neg, 'factorization', 'factorized', 'factor')
InnerExpr.register_equivalence_method(
    Neg,
    'inner_neg_mult_simplification',
    'inner_neg_mult_simplified',
    'inner_neg_mult_simplify')
