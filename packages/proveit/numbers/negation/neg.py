from proveit import (Expression, Literal, Operation, ExprRange,
                     maybe_fenced_string, maybe_fenced_latex, 
                     InnerExpr, defaults, USE_DEFAULTS, 
                     ProofFailure, relation_prover, equality_prover,
                     auto_relation_prover, auto_equality_prover,
                     SimplificationDirectives)
from proveit.logic import is_irreducible_value
from proveit.numbers.number_sets import (
        ZeroSet, Natural, NaturalPos,
        Integer, IntegerNonZero, IntegerNeg, IntegerNonPos,
        Rational, RationalNonZero, RationalPos, RationalNeg,
        RationalNonNeg, RationalNonPos,
        Real, RealNonZero, RealPos, RealNeg, RealNonNeg, RealNonPos,
        Complex, ComplexNonZero)
from proveit import a, b, c, i, j, m, n, x, y, B
from proveit.numbers import (NumberOperation, readily_provable_number_set,
                             standard_number_set)

class Neg(NumberOperation):
    # operator of the Neg operation.
    _operator_ = Literal(string_format='-', theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            distribute_over_add = True)

    def __init__(self, A, *, styles=None):
        NumberOperation.__init__(self, Neg._operator_, A, styles=styles)
        if not hasattr(self, 'operand'):
            raise ValueError("Neg must be unary! But we were given: {}".
                    format(A))

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
        If negating a Neg, undo the double negation.
        '''
        from proveit.numbers import is_numeric_rational, zero, one, Add, Mult
        canonical_operand = self.operand.canonical_form()
        if canonical_operand == zero:
            return zero # -0 = 0
        if (isinstance(canonical_operand, Mult) and 
                is_numeric_rational(canonical_operand.factors[0])):
            # Apply the negation to the rational coefficient.
            coef = canonical_operand.factors[0]
            return Mult(Neg(coef).canonical_form(),
                        *canonical_operand.factors
                        .entries[1:]).canonical_form()
        elif isinstance(canonical_operand, Add):
            # Distribute the negation over the sum.
            negated_terms = []
            for term in canonical_operand.terms:
                if isinstance(term, ExprRange):
                    neg_term = ExprRange(term.parameter, Neg(term.body),
                                         term.true_start_index,
                                         term.true_end_index)
                else:
                    neg_term = Neg(term)
                negated_terms.append(neg_term)
            return Add(*negated_terms).canonical_form() 
        elif isinstance(canonical_operand, Neg):
            return canonical_operand.operand # double negation
        elif is_numeric_rational(canonical_operand):
            if canonical_operand != self.operand:
                return Neg(canonical_operand)
            return self
        else:
            # in the following, probably don't need the
            # final canonical_form() method call at the end
            return Mult(Neg(one), canonical_operand) #.canonical_form()

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        given a number set, attempt to prove that the given expression
        is in that number set using the appropriate closure theorem
        '''
        import proveit.numbers.negation as neg_pkg
        thm = None
        if number_set == ZeroSet:
            thm = neg_pkg.neg_in_zero_set
        if number_set == Natural:
            thm = neg_pkg.nat_closure
        elif number_set == NaturalPos:
            thm = neg_pkg.nat_pos_closure
        elif number_set == Integer:
            thm = neg_pkg.int_closure
        elif number_set == IntegerNonZero:
            thm = neg_pkg.int_nonzero_closure
        elif number_set == IntegerNeg:
            thm = neg_pkg.int_neg_closure
        elif number_set == IntegerNonPos:
            thm = neg_pkg.int_nonpos_closure
        elif number_set == Rational:
            thm = neg_pkg.rational_closure
        elif number_set == RationalNonZero:
            thm = neg_pkg.rational_nonzero_closure
        elif number_set == RationalPos:
            thm = neg_pkg.rational_pos_closure
        elif number_set == RationalNeg:
            thm = neg_pkg.rational_neg_closure
        elif number_set == RationalNonNeg:
            thm = neg_pkg.rational_nonneg_closure
        elif number_set == RationalNonPos:
            thm = neg_pkg.rational_nonpos_closure
        elif number_set == Real:
            thm = neg_pkg.real_closure
        elif number_set == RealNonZero:
            thm = neg_pkg.real_nonzero_closure
        elif number_set == RealPos:
            thm = neg_pkg.real_pos_closure
        elif number_set == RealNeg:
            thm = neg_pkg.real_neg_closure
        elif number_set == RealNonNeg:
            thm = neg_pkg.real_nonneg_closure
        elif number_set == RealNonPos:
            thm = neg_pkg.real_nonpos_closure
        elif number_set == Complex:
            thm = neg_pkg.complex_closure
        elif number_set == ComplexNonZero:
            thm = neg_pkg.complex_nonzero_closure
        if thm is not None:
            return thm.instantiate({a: self.operand})
        raise NotImplementedError(
            "No negation closure theorem for set %s" %str(number_set))

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        number_set_map = {
            ZeroSet: ZeroSet,
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
        operand_ns = readily_provable_number_set(self.operand)
        if operand_ns is None: return None
        # check if operand_ns is not a standard number set
        if operand_ns not in number_set_map.keys():
            # try to replace term_ns with a std number set
            operand_ns = standard_number_set(operand_ns)
        return number_set_map[operand_ns]

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

    def readily_factorable(self, factor):
        # Return True iff 'factor' is factorable from 'self' in an
        # obvious manner.  For this Neg, it is readily factorable if
        # it is readily factorable from its operand.  If 'factor' is
        # a Neg, just use its operand.
        if self == factor:
            return True
        if isinstance(factor, Neg):
            factor = factor.operand
        return self.operand.readily_factorable(factor)

    @auto_equality_prover('factorized', 'factor')
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
                the_factors, pull, group_factors=True, group_remainder=True)
            eqn1 = operand_factor_eqn.substitution(self.inner_expr().operand)
            new_operand = operand_factor_eqn.rhs
            _x = new_operand.operands[0]
            _y = new_operand.operands[1]
            eqn2 = thm.instantiate({x:_x, y: _y}).derive_reversed()
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
