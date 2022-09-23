from proveit import Judgment, UnsatisfiedPrerequisites, prover, defaults
from proveit.logic import Equals
from proveit.relation import TransitiveRelation, total_ordering


class NumberOrderingRelation(TransitiveRelation):    
    def __init__(self, operator, lhs, rhs, *, styles):
        TransitiveRelation.__init__(self, operator, lhs, rhs,
                                    styles=styles)
        # The lower bound side of this inequality.
        # (regardless of the 'direction' style).
        self.lower = self.operands[0]
        # The upper bound side of this inequality.
        self.upper = self.operands[1]
    
    def side_effects(self, judgment):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt derive_negated, derive_relaxed (if applicable),
        and derive_reversed.
        '''
        for side_effect in TransitiveRelation.side_effects(self, judgment):
            yield side_effect
        # yield self.derive_negated # Needs to be implemented (again)
        if hasattr(self, 'derive_relaxed'):
            yield self.derive_relaxed

    def _readily_provable(self, *, check_number_sets=True,
                          must_be_direct=False,
                          check_transitive_pair=True):
        from .less import Less
        from .less_eq import LessEq
        from proveit.numbers import (
                zero, Add, Neg, greater, greater_eq, one,
                NaturalPos, IntegerNeg, IntegerNonPos, 
                less_numeric_rationals, less_eq_numeric_rationals,
                RealPos, RealNeg, RealNonNeg, RealNonPos, Complex,
                readily_provable_number_set, is_numeric_rational, 
                less_numeric_rationals, less_eq_numeric_rationals)
        lower, upper = self.lower, self.upper
        '''
        lower_cf, upper_cf = lower.canonical_form(), upper.canonical_form()
        if is_numeric_rational(lower_cf) and (
                is_numeric_rational(upper_cf)):
            # Numeric rationals can be compared directly.
            if isinstance(self, Less):
                return less_numeric_rationals(lower_cf, upper_cf)
            else:
                return less_eq_numeric_rationals(lower_cf, upper_cf)
        '''
        if isinstance(self, LessEq) and (
                Equals(self.lhs, self.rhs).readily_provable()):
            # LessEq via Equal.
            return True
        if not must_be_direct:
            judgment = self.known_similar_but_possibly_stronger_bound()
            if judgment is not None:
                # There is a similar but possibly stronger bound we can
                # derive this one from.
                return True
        if not check_number_sets:
            return False
        
        # See if we can determine the validity of the inequality
        # based upon provable number sets and how they relate to zero.
        
        # _check_order_against_zero=False to avoid infinite recursion.
        lower_ns = readily_provable_number_set(
                    lower, default=Complex, _check_order_against_zero=False)
        upper_ns = readily_provable_number_set(
                    upper, default=Complex, _check_order_against_zero=False)
        if isinstance(self, LessEq):
            if is_numeric_rational(lower) and (
                    less_eq_numeric_rationals(lower, one)
                    and NaturalPos.readily_includes(upper_ns)):
                return True
            if is_numeric_rational(upper) and (
                    less_eq_numeric_rationals(upper, Neg(one))
                    and IntegerNeg.readily_includes(lower_ns)):
                return True
            if RealNonPos.readily_includes(lower_ns) and (
                    RealNonNeg.readily_includes(upper_ns)):
                return True
        else:
            if is_numeric_rational(lower) and (
                    less_numeric_rationals(lower, one)
                    and NaturalPos.readily_includes(upper_ns)):
                return True
            if is_numeric_rational(upper) and (
                    less_numeric_rationals(upper, Neg(one))
                    and IntegerNeg.readily_includes(lower_ns)):
                return True
            if RealNonPos.readily_includes(lower_ns) and (
                    RealPos.readily_includes(upper_ns)):
                return True
            if RealNeg.readily_includes(lower_ns) and (
                    RealNonNeg.readily_includes(upper_ns)):
                return True

        """
        if ((isinstance(self.lower, Add) and 
                self.upper in self.lower.terms.entries) or
             (isinstance(self.upper, Add) and 
                self.lower in self.upper.terms.entries)):
            TODO
        """
        if check_transitive_pair:
            return TransitiveRelation._readily_provable(self)
        
        return False

    def _readily_disprovable(self, *, check_number_sets=True,
                          must_be_direct=False,
                          check_transitive_pair=True):
        from .less import Less
        from .less_eq import LessEq
        if isinstance(self, Less) and (
                LessEq(self.rhs, self.lhs).readily_provable()):
            # Not(x < y) via x ≥ y.
            return True
        return False
        
    @prover
    def conclude(self, **defaults_config):
        '''
        Automatically conclude an OrderingRelation if a canonical
        version is known that is at least as strong.
        '''
        from .less import Less
        from .less_eq import LessEq
        from proveit.numbers import is_numeric_int, is_numeric_rational
        judgment = self.known_similar_but_possibly_stronger_bound()
        '''
        lower, upper = self.lower, self.upper
        lower_cf, upper_cf = lower.canonical_form(), upper.canonical_form()
        if is_numeric_rational(lower_cf) and is_numeric_rational(upper_cf):
            if isinstance(self, LessEq) and lower_cf == upper_cf:
                return self.conclude_via_equality()
            # TODO: MAYBE USE SAME CANONICAL FORMS FOR RATIONAL COMPARISONS
        ''' 
        if judgment is not None:
            return self.conclude_from_similar_bound(judgment)
        # Explore transitive relations as a last resort.
        return TransitiveRelation.conclude(self)
        
    def known_similar_but_possibly_stronger_bound(self):
        '''
        If there is a similar but possibly stronger known relation
        based upon canonical forms, return the known Judgment.
        Otherwise, return None.
        '''
        from .less import Less
        from .less_eq import LessEq
        from proveit.numbers import (zero, one, subtract,
                                     is_numeric_int, is_numeric_rational,
                                     less_eq_numeric_rationals,
                                     less_numeric_rationals)
        canonical_form = self.canonical_form()
        is_weak = isinstance(self, LessEq)
        if is_weak:
            # x ≤ a, a ≤ b => x ≤ b
            comparator = less_eq_numeric_rationals
        else:
            # x ≤ a, a < b => x < b
            comparator = less_numeric_rationals
        if is_numeric_rational(canonical_form.lhs) and (
                is_numeric_rational(canonical_form.rhs)):
            # If the canonical form simply compares numeric rationals,
            # we should be able to readily prove a similar form.
            rhs = subtract(canonical_form.rhs, canonical_form.lhs)
            rhs = rhs.canonical_form()
            if comparator(zero, rhs):
                if is_numeric_int(rhs):
                    return self.__class__(zero, rhs)
                else:
                    # rescaled version.
                    return self.__class__(zero, one)
        desired_bound = canonical_form.rhs
        known_strong_bounds = Less.known_canonical_bounds.get(
                canonical_form.normal_lhs, tuple())
        known_weak_bounds = LessEq.known_canonical_bounds.get(
                canonical_form.normal_lhs, tuple())
        # For the case where the known bound is strong, use:
        # x < a, a ≤ b => x < b as well as x ≤ b
        for judgment, strong_bound in known_strong_bounds:
            if judgment.is_applicable():
                if (strong_bound == desired_bound or 
                        less_eq_numeric_rationals(strong_bound, 
                                                  desired_bound)):
                    return judgment
        for judgment, weak_bound in known_weak_bounds:
            if judgment.is_applicable():
                if ((is_weak and weak_bound == desired_bound) or 
                        comparator(weak_bound, desired_bound)):
                    return judgment
        return None

    @prover
    def conclude_from_known_bound(self, **defaults_config):
        '''
        Conclude this statement by using a known similar but possibly
        stronger bound based upon canonical forms.
        '''
        judgment = self.known_similar_but_possibly_stronger_bound()
        if judgment is None:
            raise UnsatisfiedPrerequisites(
                "No known bound that is similar to %s and at least "
                "as strong"%self)
        return self.conclude_from_similar_bound(judgment)

    @prover
    def conclude_from_similar_bound(self, similar_bound, 
                                      **defaults_config):
        '''
        Prove this number ordering relation given a proven (or provable)
        bound that is as strong as the desired bound w.r.t. canonical 
        forms (scaling and rearronging terms).
        '''
        from proveit.logic import Equals
        from proveit.numbers import (zero, one, Add, Neg, subtract,
                                     Less, LessEq, is_numeric_rational,
                                     simplified_numeric_rational,
                                     numeric_rational_ints)
        if isinstance(similar_bound, Judgment):
            similar_bound = similar_bound.expr
        if not isinstance(similar_bound, NumberOrderingRelation):
            raise TypeError("'similar_bound' should be a "
                            "NumberOrderingRelation")

        # Get the canonical forms and make sure they are 'similar'
        # (the same on the left side).
        canonical_form, inv_scale = (
                self._canonical_form_and_inv_scale_factor(
                        reduce_numeric_rational_form=True))
        other_canonical_form, other_inv_scale = (
                similar_bound._canonical_form_and_inv_scale_factor(
                        reduce_numeric_rational_form=True))
        if canonical_form.normal_lhs != other_canonical_form.normal_lhs:
            raise ValueError(
                    "Attempting to conclude %s from %s, but these do not "
                    "have the same canonical form lhs: %s vs %s"
                    %(self, similar_bound, canonical_form, 
                      other_canonical_form))
        
        # Obtain the difference of the canonical form right sides
        # and make sure that similar_bound is stronger than self.
        # Note:
        # x ≤ a, 0 ≤ b-a => x ≤ b
        # x ≤ a, 0 < b-a => x < b
        fails_strength_check = False
        if other_canonical_form.rhs == canonical_form.rhs:
            rhs_diff = zero
            if isinstance(similar_bound, LessEq) and isinstance(self, Less):
                fails_strength_check = True                
        else:
            rhs_diff = subtract(canonical_form.rhs,
                                other_canonical_form.rhs)
            rhs_diff = rhs_diff.canonical_form()
            assert is_numeric_rational(rhs_diff)
            if isinstance(rhs_diff, Neg):
                fails_strength_check = True
        if fails_strength_check:
            raise TypeError(
                    "'similar_bound' ` "
                    "bound than what we are trying to conclude. "
                    "%s is weaker than %s"%(similar_bound, self))
        
        # Start a sequence of transformation of the similar bound
        # to obtain the desired bound.
        known_bound = similar_bound.prove()        
        with defaults.temporary() as tmp_defaults:
            # We want full control -- no auto-simplification.
            tmp_defaults.auto_simplify = False
            tmp_defaults.replacements = set()

            # Rescale appropriately
            #   from 'similar_bound':
            denom, numer = numeric_rational_ints(other_inv_scale)
            #   to 'self':
            numer_factor, denom_factor = numeric_rational_ints(inv_scale)
            numer *= numer_factor
            denom *= denom_factor
            scale_factor = simplified_numeric_rational(numer, denom)
            # Multiply both sides (distribution will be dealt with
            # automatically when we equate expression with the 
            # same canonical forms below).
            if scale_factor != one:
                known_bound = known_bound.left_mult_both_sides(scale_factor)

            # Weaken as appropriate.
            if rhs_diff == zero:
                if isinstance(self, LessEq) and (
                        isinstance(similar_bound, Less)):
                    known_bound = known_bound.derive_relaxed()
            else:
                rhs_diff_numer, rhs_diff_denom = numeric_rational_ints(
                        rhs_diff)
                # scale the rhs diff from the canonical scaling to
                # the desired scaling.
                scaled_rhs_diff = simplified_numeric_rational(
                        rhs_diff_numer*numer_factor,
                        rhs_diff_denom*denom_factor)
                assert not isinstance(scaled_rhs_diff, Neg)
                strong = isinstance(self, Less)
                if known_bound.is_reversed():
                    # a > x => a + c > x   with c > 0
                    known_bound = known_bound.add_left(
                        scaled_rhs_diff, strong=strong)
                else:
                    # x < a => x < a + c   with c > 0
                    known_bound = known_bound.add_right(
                        scaled_rhs_diff, strong=strong)
            if isinstance(self, LessEq) and isinstance(known_bound.expr, Less):
                # weaken from < to ≤.
                known_bound = known_bound.derive_relaxed()
            
            # See if we need to add something terms to both sides,
            # making replacements to the desired form.
            lhs_diff = subtract(self.normal_lhs, known_bound.normal_lhs)
            lhs_diff = lhs_diff.simplified()
            if lhs_diff.canonical_form() != zero:
                # Replacements will be used to get the expression
                # in the desired form.
                replacements = []
                replacements.append(
                        Equals(Add(known_bound.normal_lhs, lhs_diff),
                               self.normal_lhs))
                replacements.append(
                        Equals(Add(known_bound.normal_rhs, lhs_diff),
                               self.normal_rhs))
                # Check and prove the replacments.
                for _k, replacement in enumerate(replacements):
                    assert (replacement.normal_lhs.canonical_form() == 
                            replacement.normal_rhs.canonical_form())
                    replacements[_k] = replacement.prove()
                # Add to both sides.
                known_bound = known_bound.right_add_both_sides(
                        lhs_diff, replacements=replacements)
            else:
                # Both sides should already be equal (with the same
                # canonical forms).  Make the substitutions.
                assert (self.normal_lhs.canonical_form() == 
                        known_bound.normal_lhs.canonical_form())
                assert (self.normal_rhs.canonical_form() == 
                        known_bound.normal_rhs.canonical_form())
                known_bound = known_bound.inner_expr().normal_lhs.substitute(
                        self.normal_lhs)
                known_bound = known_bound.inner_expr().normal_rhs.substitute(
                        self.normal_rhs)        
        return known_bound # Should be done!
    
    def _build_canonical_form(self):
        '''
        Returns a form of this number ordering relation in which,
        after putting both sides of the relation in canonical form,
        all terms except rational literals are moved to the left side
        and the entire relation is deterministically scaled.  All 
        relations with this same canonical form may be derived from 
        one to the other.
        '''
        return self._canonical_form_and_inv_scale_factor()[0]
        
    def _canonical_form_and_inv_scale_factor(
            self, reduce_numeric_rational_form=False):
        '''
        Returns the canonical form and the inverse scale factor used in 
        obtaining the canonical form.  Helper function for
        canonical_form.
        '''
        from proveit.numbers import (zero, one, Add, Neg, Mult, Div, 
                                     is_numeric_int, is_numeric_rational)
        # Obtain the canonical forms of both sides.
        canonical_lhs = self.normal_lhs.canonical_form()
        canonical_rhs = self.normal_rhs.canonical_form()
        # Extract the literal, rational (constant) terms to add to
        # both sides to move the constant to the right side.
        constant_terms = []
        for side, sign in zip((canonical_lhs, canonical_rhs), (-1, 1)):
            terms = side.terms if isinstance(side, Add) else [side]
            for term in terms:
                if is_numeric_rational(term):
                    if sign < 1 and term != zero:
                        term = Neg(term).canonical_form()
                    constant_terms.append(term)
        # lhs: original_lhs - original_rhs + constants
        # rhs: constants
        lhs = Add(self.normal_lhs, Neg(self.normal_rhs), *constant_terms)
        lhs = lhs.canonical_form()
        rhs = Add(*constant_terms).canonical_form()
        
        if lhs == zero:
            # Special case involving only numeric rationals (after
            # cancelations, possibly).
            if rhs == zero or isinstance(rhs, Neg):
                # This is something trivial like 5 <= 5 or
                # something untrue like 6 < 5; let's keep it close 
                # to the original.
                return (self.__class__(canonical_lhs, canonical_rhs), 
                        one)
            elif not is_numeric_rational(canonical_rhs):
                # For example, x < x + 2 converts to 0 < 1 with 2 as
                # the inverse scale factor.
                return self.__class__(zero, one), rhs                
            elif not reduce_numeric_rational_form:
                # Just use the canonical forms of each side with no
                # further manipulation.
                return self.__class__(canonical_lhs, canonical_rhs), one
            else:
                if is_numeric_int(rhs):
                    # For example, -2 < 5 converts to 0 < 7
                    return self.__class__(zero, rhs), one
                else:
                    # For example, 1/4 < 2/3 converts to 0 < 1 with 5/12
                    # as the inverse scale factor.
                    return self.__class__(zero, one), rhs
        
        # Now deterministically scale both sides.
        inv_scale_factor = one
        if isinstance(lhs, Add):
            # Choose the first term to normalize according.
            term = next(iter(lhs.terms))
            if isinstance(term, Mult) and (
                    is_numeric_rational(term.factors[0])):
                # Term with rational coefficient.
                inv_scale_factor = term.factors[0]
            else:
                # Term with no rational coefficient.
                inv_scale_factor = one # No need to rescale
        elif isinstance(lhs, Mult) and is_numeric_rational(lhs.factors[0]):
            # Scale inversely by the one and only coefficient.
            inv_scale_factor = lhs.factors[0]  
        inv_scale_factor = inv_scale_factor.canonical_form()
        if isinstance(inv_scale_factor, Neg):
            # Only resclae positively
            inv_scale_factor = inv_scale_factor.operand
        if inv_scale_factor != one:
            # Rescale
            lhs = Div(lhs, inv_scale_factor).canonical_form()
            rhs = Div(rhs, inv_scale_factor).canonical_form()
        
        # Return the expression indicating that the
        # sum of terms is less than (or equal) to a literal rational.
        return self.__class__(lhs, rhs), inv_scale_factor
    
    def _deduce_canonically_equal(self, rhs):
        '''
        Prove that this NumberOrderingRelation is equal to an expression 
        that has the same canonical form.  Do this through mutual
        implication.
        '''
        from proveit.logic import Iff
        mutual_impl = Iff(self, rhs).conclude_by_definition()
        return mutual_impl.derive_equality()
        
    @staticmethod
    def WeakRelationClass():
        from .less_eq import LessEq
        return LessEq  # <= is weaker than <

    @staticmethod
    def StrongRelationClass():
        from .less import Less
        return Less  # < is stronger than <=

    def derive_shifted(
            self,
            addend,
            addend_side='right',
            assumptions=frozenset()):
        raise NotImplementedError(
            'derive_shifted is implemented for each specific LesserRelation')
    
    def derive_added(self, other_ordering_relation, assumptions=frozenset()):
        r'''
        Add this ordering relation with another ordering relation.
        For example, if self is (a < b) and other_ordering_relation is 
        (c < d), then this derives and returns (a + c < b + d).
        '''
        from proveit.numbers import LessThan, LessThanEquals
        other = other_ordering_relation
        if not (isinstance(other, NumberOrderingRelation)):
            raise ValueError(
                "Expecting 'other_ordering_relation' to be an "
                "NumberOrderingRelation")
        if (isinstance(self, LessThan) or isinstance(self, LessThanEquals)) != (
                isinstance(other, LessThan) or isinstance(other, LessThanEquals)):
            # reverse other to be consistent with self (both less than type or
            # greater than type)
            other = other.derive_reversed()
        shifted_self = self.derive_shifted(
            other.lhs, 'right', assumptions)  # e.g., a + c < b + c
        shifted_other = other.derive_shifted(
            self.rhs, 'left', assumptions)  # e.g., b + c < b + d
        new_rel = shifted_self.apply_transitivity(
            shifted_other)  # e.g., a + c < b + d
        # Match style (e.g., use '>' if 'direction' is 'reversed').
        return new_rel.with_mimicked_style(self)

    def readily_in_bool(self):
        '''
        A number ordering relation is a boolean iff the operands 
        are Real.
        '''
        from proveit.logic import InSet
        from proveit.numbers import Real
        return (InSet(self.lhs, Real).readily_provable() and 
                InSet(self.rhs, Real).readily_provable())

    @prover
    def square_both_sides(self, **defaults_config):
        from proveit.numbers import two
        # Match style (e.g., use '>' if 'direction' is 'reversed').
        new_rel = self.exponentiate_both_sides(two)
        # Match style (e.g., use '>' if 'direction' is 'reversed').
        return new_rel.with_mimicked_style(self)
        
    @prover
    def square_root_both_sides(self, **defaults_config):
        from proveit.numbers import frac, one, two, Exp
        new_rel = self.exponentiate_both_sides(frac(one, two))
        if (isinstance(new_rel.lhs, Exp)
                and new_rel.lhs.exponent == frac(one, two)):
            new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        if (isinstance(new_rel.rhs, Exp)
                and new_rel.rhs.exponent == frac(one, two)):
            new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        # Match style (e.g., use '>' if 'direction' is 'reversed').
        return new_rel.with_mimicked_style(self)

def _make_term(rational_coef, remainder):
    '''
    Make an expression that multiplies a rational coefficient and a 
    remainder.  The coefficient should be in the form of a pair of 
    integers for the numerator and denominator respectively.
    Assume it coefficient is already simplified.
    '''
    from proveit.numbers import Mult, Div, num
    numer, denom = rational_coef
    assert isinstance(numer, int)
    assert isinstance(denom, int)
    if numer == denom == 1:
        return remainder
    if denom == 1:
        coef = num(numer)
    else:
        coef = Div(num(numer), num(denom))
    if remainder == one:
        return coef
    elif isinstance(remainder, Mult):
        return Mult(coef, *remainder.factors)
    else:
        return Mult(coef, remainder)

def number_ordering(*relations):
    '''
    Return a conjunction of number ordering relations
    with a total-ordering style; for example,
    a < b <= c = d < e
    '''
    from proveit.logic import Equals
    for relation in relations:
        if (not isinstance(relation, NumberOrderingRelation) and
               not isinstance(relation, Equals)):
            raise TypeError("For a set inclusion ordering expression, "
                            "all relations must be either "
                            "NumberOrderingRelation or Equals objects.")
    return total_ordering(*relations)
