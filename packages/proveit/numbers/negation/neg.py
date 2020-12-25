from proveit import Literal, Operation, maybe_fenced_string, maybe_fenced_latex, InnerExpr, USE_DEFAULTS, ProofFailure
from proveit.logic import is_irreducible_value
from proveit.numbers.number_sets import Integer, Real, Complex
from proveit import a, b, m, n, x, y, B


class Neg(Operation):
    # operator of the Neg operation.
    _operator_ = Literal(string_format='-', theory=__file__)

    def __init__(self, A):
        Operation.__init__(self, Neg._operator_, A)

    def irreducible_value(self):
        from proveit.numbers import zero
        return is_irreducible_value(self.operand) and self.operand != zero

    def deduce_in_number_set(self, NumberSet, assumptions=USE_DEFAULTS):
        '''
        given a number set, attempt to prove that the given expression is in that
        number set using the appropriate closure theorem
        '''
        from . import int_closure, real_closure, complex_closure
        from proveit.logic import InSet
        if NumberSet == Integer:
            return int_closure.instantiate({a: self.operand})
        elif NumberSet == Real:
            return real_closure.instantiate({a: self.operand})
        elif NumberSet == Complex:
            return complex_closure.instantiate({a: self.operand})
        else:
            raise ProofFailure(
                InSet(
                    self,
                    NumberSet),
                assumptions,
                "No negation closure theorem for set %s" %
                str(NumberSet))

    def do_reduced_simplification(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Derive and return this negation expression equated with a simpler form.
        Deals with double negation specifically.
        '''
        from proveit.relation import TransRelUpdater

        expr = self
        # For convenience updating our equation:
        eq = TransRelUpdater(expr, assumptions)
        # Handle double negation:
        if isinstance(self.operand, Neg):
            # simplify double negation
            expr = eq.update(self.double_neg_simplification(assumptions))
            # simplify what is inside the double-negation.
            expr = eq.update(expr.simplification(assumptions))
        return eq.relation

    def do_reduced_evaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Only handles -0 = 0 or double negation.
        '''
        from proveit.logic import EvaluationError
        from . import negated_zero
        from proveit.numbers import zero
        if self.operand == zero:
            return negated_zero
        if isinstance(
                self.operand,
                Neg) and is_irreducible_value(
                self.operand.operand):
            return self.double_neg_simplification(assumptions)
        raise EvaluationError(self, assumptions)

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
        from proveit.numbers import Add, num
        from proveit.relation import TransRelUpdater
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr, assumptions)

        if isinstance(self.operand, Add):
            # Distribute negation through a sum.
            add_expr = self.operand
            if len(add_expr.operands) == 2:
                # special case of 2 operands
                if isinstance(add_expr.operands[1], Neg):
                    expr = eq.update(distribute_neg_through_subtract.instantiate(
                        {a: add_expr.operands[0], b: add_expr.operands[1].operand}, assumptions=assumptions))
                else:
                    expr = eq.update(distribute_neg_through_binary_sum.instantiate(
                        {a: add_expr.operands[0], b: add_expr.operands[1]}, assumptions=assumptions))
            else:
                # distribute the negation over the sum
                expr = eq.update(distribute_neg_through_sum.instantiate(
                    {n: num(len(add_expr.operands)), xx: add_expr.operands}), assumptions=assumptions)
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
        if hasattr(self.operand, 'factor'):
            operand_factor_eqn = self.operand.factor(
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
            return eqn1.apply_transitivity(eqn2)
        else:
            if self.operand != the_factor:
                raise ValueError("%s is a factor in %s!" % (the_factor, self))
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
        from proveit.numbers import Mult, num
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

        if len(mult_expr.operands) == 2:
            if idx == 0:
                return mult_neg_left_double.instantiate(
                    {a: mult_expr.operands[1]}, assumptions=assumptions)
            else:
                return mult_neg_right_double.instantiate(
                    {a: mult_expr.operands[0]}, assumptions=assumptions)
        a_val = mult_expr.operands[:idx]
        b_val = mult_expr.operands[idx]
        c_val = mult_expr.operands[idx + 1:]
        m_val = num(len(a_val))
        n_val = num(len(c_val))
        return mult_neg_any_double.instantiate(
            {m: m_val, n: n_val, AA: a_val, B: b_val, CC: c_val}, assumptions=assumptions)


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
