from proveit import (defaults, Literal, Operation, ExprRange, InnerExpr,
                     ProofFailure, USE_DEFAULTS, relation_prover,
                     equality_prover)
from proveit import a, b, c, n, r, x, theta
from proveit.logic import InSet
from proveit.logic.sets import ProperSubset, SubsetEq
from proveit.numbers import NumberOperation


class Abs(NumberOperation):
    # operator of the Abs operation.
    _operator_ = Literal(string_format='Abs', theory=__file__)

    def __init__(self, A, *, styles=None):
        NumberOperation.__init__(self, Abs._operator_, A, 
                                 styles=styles)

    def string(self, **kwargs):
        return '|' + self.operand.string() + '|'

    def latex(self, **kwargs):
        return r'\left|' + self.operand.latex() + r'\right|'

    def not_equal(self, rhs, assumptions=USE_DEFAULTS):
        # accessed from conclude() method in not_equals.py
        from . import abs_not_eq_zero
        from proveit.logic import NotEquals
        from proveit.numbers import zero
        if rhs == zero:
            return abs_not_eq_zero.instantiate(
                {a: self.operand}, assumptions=assumptions)
        raise NotEquals(self, zero).conclude_as_folded(assumptions)

    def deduce_greater_than_equals_zero(self, assumptions=USE_DEFAULTS):
        from . import abs_is_non_neg
        return abs_is_non_neg.instantiate(
            {a: self.operand}, assumptions=assumptions)

    @equality_prover('distributed', 'distribute')
    def distribution(self, **defaults_config):
        '''
        Equate this absolute value with its distribution over a product
        or fraction.
        '''
        from . import abs_frac, abs_prod, abs_even
        from proveit import n, x
        from proveit.numbers import Neg, Div, Mult
        if isinstance(self.operand, Neg):
            return abs_even.instantiate({x: self.operand.operand})
        elif isinstance(self.operand, Div):
            return abs_frac.instantiate(
                {a: self.operand.numerator, b: self.operand.denominator})
        elif isinstance(self.operand, Mult):
            _x = self.operand.operands
            _n = _x.num_elements()
            return abs_prod.instantiate({n: _n, x: _x})
        else:
            raise ValueError(
                'Unsupported operand type for Abs.distribution() '
                'method: ', str(self.operand.__class__))

    @equality_prover('abs_eliminated', 'abs_eliminate')
    def abs_elimination(self, operand_type=None, **defaults_config):
        '''
        For some |x| expression, deduce either |x| = x (the default) OR
        |x| = -x (for operand_type = 'negative'). Assumptions may be
        needed to deduce x >= 0 or x < 0, respectively.
        '''
        from proveit.numbers import LessEq, zero
        from . import abs_non_neg_elim, abs_neg_elim
        if operand_type is None:
            # LessEq.sort uses a bidirectional search which should
            # be fairly efficient, as long as there aren't too
            # many known relationship directly or indirectly involving
            # self.operand or zero.
            relation_with_zero = LessEq.sort([zero, self.operand])
            if relation_with_zero.normal_lhs == zero:
                operand_type = 'non-negative'
            else:
                operand_type = 'negative'        
        # deduce_non_neg(self.operand, assumptions) # NOT YET IMPLEMENTED
        if operand_type is None or operand_type == 'non-negative':
            return abs_non_neg_elim.instantiate({x: self.operand})
        elif operand_type == 'negative':
            return abs_neg_elim.instantiate({x: self.operand})
        else:
            raise ValueError(
                "Unsupported operand type for Abs.abs_elimination() "
                "method; operand type should be omitted or specified "
                "as 'negative' or 'non-negative', but instead was "
                "given as operand_type = {}.".format(operand_type))

    @equality_prover('double_abs_eliminated', 'double_abs_eliminate')
    def double_abs_elimination(self, **defaults_config):
        '''
        ||x|| = |x| given x is complex.
        '''
        from . import double_abs_elem
        if not isinstance(self.operand, Abs):
            raise ValueError("'double_abs_elimination' is only applicable "
                             "for double absolute value cases, not %s"
                             %self)
        return double_abs_elem.instantiate({x:self.operand.operand})
    
    @equality_prover('shallow_evaluated', 'shallow_evaluate')
    def shallow_evaluation(self, **defaults_config):
        '''
        Equates the absolute value of a literal to its
        irreducible representation.
        '''
        from proveit.numbers import Neg
        from proveit.logic import EvaluationError, is_irreducible_value
        if not is_irreducible_value(self.operand):
            # The operand must be irreducible in order to do a
            # shallow evaluation.
            raise EvaluationError(self)
        if isinstance(self.operand, Neg):
            # |-x| where 'x' is a literal.
            return self.distribution()
        else:
            # If the operand is irreducible, we can just use 
            # abs_elimination.
            return self.abs_elimination()

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, **defaults_config):
        '''
        Returns a proven simplification equation for this Abs
        expression assuming the operand has been simplified.
        
        Handles a number of absolute value simplifications:
            1. ||x|| = |x| given x is complex
            2. |x| = x given x ≥ 0
            3. |x| = -x given x ≤ 0
                             (may try to prove this if easy to do)
            4. |-x| = |x|
            5. |x_1 * ... * x_n| = |x_1| * ... * |x_n|
            6. |a / b| = |a| / |b|
            7. |exp(i a)| = 1 given a in Real
            8. |r exp(i a) - r exp(i b)| = 2 r sin(|a - b|/2)
                given a and b in Real.
            9. |x_1 + ... + x_n| = +/-(x_1 + ... + x_n) if
               the terms are known to be all non-negative
               or all non-positive.
        '''
        from proveit.logic import Equals
        from proveit.numbers import e, Add, Neg, LessEq, Mult, Div, Exp
        from proveit.numbers import zero, RealNonNeg, RealNonPos
        # among other things, convert any assumptions=None
        # to assumptions=() (thus averting len(None) errors)

        # Check if we have an established relationship between
        # self.operand and zero.
        if (LessEq(zero, self.operand).proven() or
                LessEq(self.operand, zero).proven()):
            # Either |x| = x or |x| = -x depending upon the sign
            # of x (comparison with zero).
            return self.abs_elimination()
        
        if isinstance(self.operand, Abs):
            # Double absolute-value.  We can remove one of them.
            return self.double_abs_elimination()

        # Distribute over a product or division.
        if (isinstance(self.operand, Mult) or isinstance(self.operand, Div)
                or isinstance(self.operand, Neg)):
            # Let's distribute the absolute values over the product
            # or division (the absolute value of the factors/components
            # will be simplified seperately if auto_simplify is True).
            return self.distribution()

        # |exp(i a)| = 1
        if isinstance(self.operand, Exp) and self.operand.base == e:
            try:
                # Grab the polar coordinate angle without automation so we 
                # don't waste time if it isn't in a unit complex polar form
                # (or obviously equivalent to this form).
                return self.unit_length_simplification(automation=False)
            except ValueError:
                # Not in a complex polar form.
                pass

        # |r exp(i a) - r exp(i b)| = 2 r sin(|a - b|/2)
        if (isinstance(self.operand, Add) and 
                self.operand.operands.is_double()):
            try:
                # Grab polar coordinates without automation so we don't
                # waste time if it isn't in a complex polar form (or 
                # obviously equivalent to this form).
                return self.chord_length_simplification(automation=False)
            except ValueError:
                # Not in a complex polar form.
                pass

        # |x_1 + ... + x_n| = +/-(x_1 + ... + x_n)
        # if the terms are known to be all non-negative or all
        # non-positive.
        if isinstance(self.operand, Add):
            all_nonneg = True
            all_nonpos = True
            for term in self.operand.terms:
                # Note that "not proven" is not the same as "disproven".
                # Not proven means there is something we do not know.
                # Disproven means that we do know the converse.
                if all_nonneg and not LessEq(zero, term).proven():
                    all_nonneg = False
                if all_nonpos and not LessEq(term, zero).proven():
                    all_nonpos = False
            if all_nonpos:
                InSet(self.operand, RealNonPos).prove()
            elif all_nonneg:
                InSet(self.operand, RealNonNeg).prove()
            if all_nonpos or all_nonneg:
                # Do another pass now that we know the sign of
                # the operand.
                return self.shallow_simplification()

        # Default is no simplification.
        return Equals(self, self).prove()

    @equality_prover('reversed_difference', 'reverse_difference')
    def difference_reversal(self, **defaults_config):
        '''
        Derive |a - b| = |b - a|.
        '''
        from proveit.numbers import Add, Neg
        from . import abs_diff_reversal
        if not (isinstance(self.operand, Add) and
                self.operand.operands.is_double() and
                isinstance(self.operand.operands[1], Neg)):
            raise ValueError("Abs.difference_reversal is only applicable "
                             "for an expression of the form |a - b|, not %s"
                             %self)
        _a = self.operand.operands[0]
        _b = self.operand.operands[1].operand
        return abs_diff_reversal.instantiate({a:_a, b:_b})

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given expression is in that number
        set using the appropriate closure theorem.
        '''
        from proveit.numbers.absolute_value import (
            abs_rational_closure, abs_rational_non_zero_closure,
            abs_complex_closure, abs_nonzero_closure,
            abs_complex_closure_non_neg_real)
        from proveit.numbers import (
            Rational, RationalNonZero, RationalPos, RationalNeg,
            RationalNonNeg, Real, RealNonNeg, RealPos)

        thm = None
        if number_set in (RationalPos, RationalNonZero):
            thm = abs_rational_non_zero_closure
        elif number_set in (Rational, RationalNonNeg, RationalNeg):
            thm = abs_rational_closure
        elif number_set == Real:
            thm = abs_complex_closure
        elif number_set == RealPos:
            thm = abs_nonzero_closure
        elif number_set == RealNonNeg:
            thm = abs_complex_closure_non_neg_real

        if thm is not None:
            in_set = thm.instantiate({a: self.operand})
            if in_set.domain == number_set:
                # Exactly the domain we were looking for.
                return in_set
            # We must have proven we were in a subset of the
            # one we were looking for.
            return InSet(self, number_set).prove()

        # To be thorough and a little more general, we check if the
        # specified number_set is already proven to *contain* one of
        # the number sets we have theorems for -- for example,
        #     Y=Complex contain X=Real, and
        #     Y=(-1, inf) contains X=RealPos,
        # but we don't have specific thms for those supersets Y.
        # If so, use the appropiate thm to determine that self is in X,
        # then prove that self must also be in Y since Y contains X.
        if SubsetEq(Real, number_set).proven():
            abs_complex_closure.instantiate({a: self.operand})
            return InSet(self, number_set).prove()
        if SubsetEq(RealPos, number_set).proven():
            abs_nonzero_closure.instantiate({a: self.operand})
            return InSet(self, number_set).prove()
        if SubsetEq(RealNonNeg, number_set).proven():
            abs_complex_closure_non_neg_real.instantiate({a: self.operand})
            return InSet(self, number_set).prove()

        # otherwise, we just don't have the right thm to make it work
        raise NotImplementedError(
            "'Abs.deduce_in_number_set()' not implemented for "
            "the %s set" % str(number_set))

    @equality_prover('unit_length_simplified', 'unit_length_simplify')
    def unit_length_simplification(self, **defaults_config):
        '''
        |exp(i * theta)| = 1 simplification given theta in Real.
        '''
        from proveit.numbers import unit_length_complex_polar_angle
        from . import complex_unit_length
        replacements = set()
        _theta = unit_length_complex_polar_angle(
                self.operand, reductions=replacements)
        # |exp(i*theta)| = 1
        return complex_unit_length.instantiate(
                {theta:_theta}, replacements=replacements)

    @equality_prover('chord_length_simplified', 'chord_length_simplify')
    def chord_length_simplification(self, **defaults_config):
        '''
        |r exp(i a) - r exp(i b)| = 2 r sin(|a - b|/2)   or
        |x exp(i a) - x exp(i b)| = 2 |x| sin(|a - b|/2)
        simplification given a, b in Real and either r in RealNonNeg
        or x in Real (depending upon what is known).
        '''
        from proveit.numbers import (one, two, Add, Neg, subtract, Div,
                                     complex_polar_coordinates)
        from proveit.trigonometry import (complex_unit_circle_chord_length,
                                          complex_circle_chord_length)
        def raise_not_valid_form():
            raise ValueError(
                    "Complex circle coord length is only applicable to "
                    "expressions of the form |r exp(i a) - r exp(i b)| "
                    "or obviously equivalent. "
                    "%s does not qualify."%self)
            
        if not (isinstance(self.operand, Add) and 
                self.operand.operands.is_double()):
            raise_not_valid_form()
        
        replacements = set()
        # Grab polar coordinates without automation so we don't
        # waste time if it isn't in a complex polar form (or 
        # obviously equivalent to this form).
        term1 = self.operand.terms[0]
        term2 = self.operand.terms[1]
        if isinstance(term2, Neg):
            term2 = term2.operand
        else:
            term2 = Neg(term2)
            replacements.add(Neg(term2).double_neg_simplification())
        _r1, _theta1 = complex_polar_coordinates(
                term1, reductions=replacements)
        _r2, _theta2 = complex_polar_coordinates(
                term2, reductions=replacements)
        if _r1 == _r2:
            # Only applicable if the magnitudes are the same.
            angle = Div(Abs(subtract(_theta1, _theta2)), two)
            replacements.add(angle.simplification())
            if _r1 == one:
                return complex_unit_circle_chord_length.instantiate(
                        {a:_theta1, b:_theta2}, replacements=replacements)
            else:
                return complex_circle_chord_length.instantiate(
                        {r: _r1, a:_theta1, b:_theta2}, 
                        replacements=replacements)
        raise_not_valid_form()

    @relation_prover
    def deduce_triangle_bound(self, **defaults_config):
        '''
        Return the proven triangle bound (or generalized triangle bound)
        of this absolute value.  For example,
            |a + b| ≤ |a| + |b|
        or
            |x_1 + ... + x_n| ≤ |x_1| + ... + |x_n|
        for the generalized triangle bound.  The terms of the sum
        must be complex numbers.
        '''
        from proveit.numbers import Add, Sum
        from . import triangle_inequality, generalized_triangle_inequality
        if isinstance(self.operand, Sum):
            # We should add a theorem for the triangle bound applicable
            # to a general summation.
            raise NotImplementedError("The triangle bound for a summation "
                                      "has not been implemented just yet.")
        if not isinstance(self.operand, Add):
            raise ValueError("The triangle bound is only applicable on "
                             "the absolute value over a sum, not %s")
        terms = self.operand.terms
        if terms.is_double():
            return triangle_inequality.instantiate({a:terms[0], b:terms[1]})
        else:
            _n = terms.num_elements()
            return generalized_triangle_inequality.instantiate(
                    {n:_n, x:terms})

    @relation_prover
    def deduce_strict_upper_bound(self, bound, **defaults_config):
        # Deduce that this absolute value has the given strict lower
        # bound by bounding the operand.  For example,
        #   |a| < c    given    -c < a < c.
        from . import strict_upper_bound
        return strict_upper_bound.instantiate(
                {a:self.operand, c:bound})

    @relation_prover
    def deduce_weak_upper_bound(self, bound,**defaults_config):
        # Deduce that this absolute value has the given weak lower
        # bound by bounding the operand.  For example,
        #   |a| ≤ c    given    -c ≤ a ≤ c.
        from . import weak_upper_bound
        return weak_upper_bound.instantiate(
                {a:self.operand, c:bound})
    
    @relation_prover
    def deduce_positive(self, **defaults_config):
        # Deduce that this absolute value is greater than zero
        # given its argument is not equal zero.
        from proveit.numbers import RealPos, zero, greater
        InSet(self, RealPos).prove()
        return greater(self, zero).prove()

def is_equal_to_or_subset_eq_of(
        number_set, equal_sets=None, subset_sets=None, subset_eq_sets=None,
        assumptions=None):
    '''
    A utility function used in the do_reduced_simplification() method
    to test whether the number set specified by number_set:
    • is equal to any of the number sets provided in the list of
      equal_sets
    • OR is already known/proven to be a proper subset of any of the
      number sets provided in the list of subset_sets,
    • OR is already known/proven to be an improper subset of any of the
      number sets provided in the list of subset_eq_sets,
    returning True at the first such equality, subset, or subset_eq
    relation found to be True.
    '''
    # among other things, convert any assumptions=None
    # to assumptions=() (thus averting len(None) errors)
    assumptions = defaults.checked_assumptions(assumptions)

    if equal_sets is not None:
        for temp_set in equal_sets:
            if number_set == temp_set:
                return True
    if subset_eq_sets is not None:
        for temp_set in subset_eq_sets:
            if SubsetEq(number_set, temp_set).proven(assumptions):
                return True
    if subset_sets is not None:
        for temp_set in subset_sets:
            if ProperSubset(number_set, temp_set).proven(assumptions):
                return True
    return False
