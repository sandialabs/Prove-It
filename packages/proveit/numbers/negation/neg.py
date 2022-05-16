from proveit import (Expression, Literal, Operation, maybe_fenced_string, 
                     maybe_fenced_latex, InnerExpr, defaults, USE_DEFAULTS, 
                     ProofFailure, relation_prover, equality_prover,
                     SimplificationDirectives)
from proveit.logic import is_irreducible_value
from proveit.numbers.number_sets import (
        Natural, NaturalPos,
        Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
        Rational, RationalNonZero, RationalPos, RationalNeg,
        RationalNonNeg, RationalNonPos,
        Real, RealNonZero, RealPos, RealNeg, RealNonNeg, RealNonPos,
        Complex, ComplexNonZero)
from proveit import a, b, c, i, j, m, n, x, y, B
from proveit.numbers import (NumberOperation, deduce_number_set,
                             standard_number_set)

class Neg(NumberOperation):
    # operator of the Neg operation.
    _operator_ = Literal(string_format='-', theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            distribute_over_add = True)

    def __init__(self, A, *, styles=None):
        NumberOperation.__init__(self, Neg._operator_, A, styles=styles)

    def style_options(self):
        '''
        Return the StyleOptions object for this Neg expression.
        '''
        options = Operation.style_options(self)
        options.add_option(
            name='notation_in_add',
            description=("When contained in an Add, use 'subtraction' "
                         "or 'explicit_negation': "
                         "For example, 'a - b' versus 'a + (-b)'."),
            default='subtraction',
            related_methods=('with_subtraction_notation',
                             'without_subtraction_notation'))
        return options

    def with_subtraction_notation(self):
        return self.with_styles(notation_in_add='subtraction')

    def without_subtraction_notation(self):
        return self.with_styles(notation_in_add='explicit_negation')

    def use_subtraction_notation(self):
        '''
        Return True if subtraction notation should be used within
        an Add operation: e.g., a - b.
        '''
        return self.get_style('notation_in_add') == 'subtraction'

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        call_strs = Operation.remake_with_style_calls(self)
        if not self.use_subtraction_notation():
            call_strs.append('without_subtraction_notation()')
        return call_strs

    def is_irreducible_value(self):
        from proveit.numbers import zero
        if isinstance(self.operand, Neg):
            return False # double negation is reducible
        return is_irreducible_value(self.operand) and self.operand != zero

    def _build_canonical_form(self):
        '''
        If negating a Mult with a nontrivial coefficient, pull the 
        negation into its coefficient.
        If negating an Add, distribute over the sum.
        '''
        from proveit.numbers import is_literal_rational, Add, Mult
        canonical_operand = self.operand.canonical_form()
        if (isinstance(canonical_operand, Mult) and 
                is_literal_rational(canonical_operand.factors[0])):
            # Apply the negation to the rational coefficient.
            coef = canonical_operand.factors[0]
            return Mult(Neg(coef).canonical_form(),
                        *canonical_operand.factors[1:])
        elif isinstance(canonical_operand, Add):
            # Distribute the negation over the sum.
            _sum = Add(*[Neg(term) for term in canonical_operand.terms])
            return _sum.canonical_form() 
        return self

    def _deduce_equality(self, equality):
        '''
        Prove that this Neg is equal to an expression that has the
        same canonical form.
        '''
        from proveit.logic import Equals
        from proveit.numbers import zero, Add
        from proveit.numbers.negation import negated_zero
        if isinstance(equality.rhs, Neg):
            # Both sides are negated.  Just equate the operands and
            # substitute.
            return equality.conclude_via_direct_substitution()

        lhs_operand_canonical_form = equality.lhs.operand.canonical_form()
        rhs_canonical_form = equality.rhs.canonical_form()
        if lhs_operand_canonical_form == rhs_canonical_form == zero:
            # -0 = 0 is a special case.
            Equals(equality.lhs.operand, zero).prove()
            Equals(equality.rhs, zero).prove()
            # substitute on the left then on the right.
            left_subbed = negated_zero.inner_expr().lhs.operand.substitute(
                    equality.lhs.operand)
            return left_subbed.inner_expr().rhs.substitute(equality.rhs)
        
        if isinstance(equality.lhs.operand, Add):
            # Distribute through an addition.
            distribution = equality.lhs.distribution()
            distrubution_eq = Equals(distribution.rhs, equality.rhs).prove()
            return distribution.apply_transitivity(distrubution_eq)
        
        #if isinstance(equality.lhs.operand, Mult):
            
        

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

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most
        restrictive standard number set we can readily know.
        '''
        number_set_map = {
            NaturalPos: IntegerNeg,
            IntegerNeg: NaturalPos,
            Natural: IntegerNonPos,
            IntegerNonPos: Natural,
            IntegerNonZero: IntegerNonZero,
            Integer: Integer,
            RationalPos: RationalNeg,
            RationalNeg: RationalPos,
            RationalNonNeg: RationalNonPos,
            RationalNonPos: RationalNonNeg,
            RationalNonZero: RationalNonZero,
            Rational: Rational,
            RealPos: RealNeg,
            RealNeg: RealPos,
            RealNonNeg: RealNonPos,
            RealNonPos: RealNonNeg,
            RealNonZero: RealNonZero,
            Real: Real,
            ComplexNonZero: ComplexNonZero,
            Complex: Complex
            }
        operand_ns = deduce_number_set(self.operand).domain
        # check if operand_ns is not a standard number set
        if operand_ns not in number_set_map.keys():
            # try to replace term_ns with a std number set
            operand_ns = standard_number_set(operand_ns)
        return self.deduce_in_number_set(number_set_map[operand_ns])

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Neg
        expression assuming the operands have been simplified.
        
        Handle negation of 0, double negation, and distribution
        over a sum.
        '''
        from . import negated_zero
        from proveit.numbers import Add, zero
        
        if must_evaluate and not is_irreducible_value(self.operand):
            # The simplification of the operands may not have
            # worked hard enough.  Let's work harder if we
            # must evaluate.
            self.operand.evaluation()
            return self.evaluation()

        if self.operand == zero:
            return negated_zero
        
        # Handle double negation:
        if isinstance(self.operand, Neg):
            # simplify double negation
            return self.double_neg_simplification()
        
        if Neg._simplification_directives_.distribute_over_add:
            # Handle distribution:
            if isinstance(self.operand, Add):
                return self.distribution(auto_simplify=True)
        
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
    def factorization(self, the_factors, pull="left", group_factors=None,
                      group_remainder=None, **defaults_config):
        '''
        Pull out the factor(s) from a negated expression, pulling it 
        either to the "left" or "right".  group_factors and 
        group_remainder are not relevant here but kept for 
        compatibility with other factor methods.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are
        in the Complex numbers so that the associative and commutation
        theorems are applicable.
        FACTORING FROM NEGATION FROM A SUM NOT IMPLEMENTED YET.
        '''
        from . import (neg_times_pos, pos_times_neg, mult_neg_one_left,
                       mult_neg_one_right)
        if isinstance(the_factors, Neg):
            if pull == 'left':
                thm = neg_times_pos
            else:
                thm = pos_times_neg
            the_factors = the_factors.operand
        else:
            if pull == 'left':
                thm = pos_times_neg
            else:
                thm = neg_times_pos
        if self.operand == the_factors:
            if thm == neg_times_pos:
                thm = mult_neg_one_left
            if thm == pos_times_neg:
                thm = mult_neg_one_right
            return thm.instantiate(
                {x: self.operand}, auto_simplify=False).derive_reversed()
        elif hasattr(self.operand, 'factorization'):
            operand_factor_eqn = self.operand.factorization(
                the_factors, pull, group_factors=True, group_remainder=True,
                preserve_all=True)
            eqn1 = operand_factor_eqn.substitution(self.inner_expr().operand)
            new_operand = operand_factor_eqn.rhs
            eqn2 = thm.instantiate(
                {x: new_operand.operands[0], y: new_operand.operands[1]},
                auto_simplify=False, preserve_expr=eqn1.rhs
                ).derive_reversed()
            return eqn1.apply_transitivity(eqn2)
        else:
            raise ValueError("%s is not a factor in %s!" 
                             % (the_factors, self))

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
        from proveit.numbers.multiplication import (
                mult_neg_left_double, mult_neg_right_double, 
                mult_neg_any_double)

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
                    {x: mult_expr.operands[0].operand,
                     y: mult_expr.operands[1]})
            else:
                return mult_neg_right_double.instantiate(
                    {x: mult_expr.operands[0],
                     y: mult_expr.operands[1].operand})

        _a_sub = mult_expr.operands[:idx]
        _b_sub = mult_expr.operands[idx].operand
        _c_sub = mult_expr.operands[idx + 1:]
        _i_sub = _a_sub.num_elements()
        _j_sub = _c_sub.num_elements()
        return mult_neg_any_double.instantiate(
            {i: _i_sub, j: _j_sub, a: _a_sub, b: _b_sub, c: _c_sub})

    @relation_prover
    def bound_via_operand_bound(self, operand_relation, **defaults_config):
        '''
        Deduce a bound on this Neg object given a bound on its
        operand. For example, suppose x = Neg(y) and we know that
        y >= 2. Then x.bound_via_operand_bound(y >= 2) returns
        x <= 2.
        Also see NumberOperation.deduce_bound and compare to the
        bound_via_operand_bound() method found in the Div class.
        '''
        from proveit import Judgment
        from proveit.numbers import Less, LessEq, NumberOrderingRelation
        if isinstance(operand_relation, Judgment):
            operand_relation = operand_relation.expr
        if not isinstance(operand_relation, NumberOrderingRelation):
            raise TypeError(
                "In Neg.bound_via_operand_bound(), the 'operand_relation' "
                "argument is expected to be a number relation (<, >, ≤, or ≥), "
                "but instead was {}.".format(operand_relation))

        lhs = operand_relation.lhs

        if lhs != self.operand:
            raise ValueError(
                    "In Neg.bound_via_operand_bound(), the left side of "
                    "the 'operand_relation' argument {0} is expected to "
                    "match the Neg() operand {1}.".
                    format(operand_relation, self.operand))

        _x_sub = operand_relation.normal_lhs
        _y_sub = operand_relation.normal_rhs

        if isinstance(operand_relation, LessEq):
            from proveit.numbers.negation import negated_weak_bound
            bound = negated_weak_bound.instantiate({x: _x_sub, y: _y_sub})
        elif isinstance(operand_relation, Less):
            from proveit.numbers.negation import negated_strong_bound
            bound = negated_strong_bound.instantiate({x: _x_sub, y: _y_sub})
        else:
            raise TypeError(
                    "In Neg.bound_via_operand_bound(), the 'operand_relation' "
                    "argument is expected to be a 'Less', 'LessEq', 'greater', "
                    "or 'greater_eq' relation. Instead we have {}.".
                    format(operand_relation))

        if bound.rhs == self:
            return bound.with_direction_reversed()
        return bound

def negated(expr):
    ''' 
    Returns the negated form of this expression.
    If the original is a Neg expression, return its operand
    (accounting for the double-negation);
    otherwise, return the Neg of the original.
    '''
    if isinstance(expr, Neg):
        return expr.operand
    return Neg(expr)
