from proveit import Judgment, UnsatisfiedPrerequisites, prover, defaults
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
    
    @prover
    def conclude(self, **defaults_config):
        '''
        Automatically conclude an OrderingRelation if a canonical
        version is known that is at least as strong.
        '''
        return self.conclude_from_known_bound()

    @prover
    def conclude_from_known_bound(self, **defaults_config):
        from proveit.numbers import (less_eq_literal_rationals,
                                     less_literal_rationals)
        from .less import Less
        from .less_eq import LessEq
        canonical_form = self.canonical_form()
        desired_bound = canonical_form.rhs
        known_strong_bounds = Less.known_canonical_bounds.get(
                canonical_form.lhs, tuple())
        known_weak_bounds = LessEq.known_canonical_bounds.get(
                canonical_form.lhs, tuple())
        # For the case where the known bound is strong, use:
        # x < a, a ≤ b => x < b as well as x ≤ b
        comparator = less_eq_literal_rationals
        for judgment, strong_bound in known_strong_bounds:
            if judgment.is_applicable():
                if (strong_bound == desired_bound or 
                        comparator(strong_bound, desired_bound)):
                    return self.conclude_from_similar_bound(judgment)
        is_weak = isinstance(self, LessEq)
        if is_weak:
            # x ≤ a, a ≤ b => x ≤ b
            comparator = less_eq_literal_rationals
        else:
            # x ≤ a, a < b => x < b
            comparator = less_literal_rationals
        for judgment, weak_bound in known_weak_bounds:
            if judgment.is_applicable():
                if ((is_weak and weak_bound == desired_bound) or 
                        comparator(weak_bound, desired_bound)):
                    return self.conclude_from_similar_bound(judgment)  
        raise UnsatisfiedPrerequisites(
                "No known bound that is similar to %s and at least "
                "as strong"%self)
    
    @prover
    def conclude_from_similar_bound(self, similar_bound, 
                                      **defaults_config):
        '''
        Prove this number ordering relation given a proven (or provable)
        bound that is as strong as the desired bound w.r.t. canonical 
        forms (scaling and rearronging terms).
        '''
        from proveit.logic import Equals
        from proveit.numbers import (zero, Add, Neg, subtract,
                                     Less, LessEq, is_literal_rational,
                                     simplified_rational_expr,
                                     literal_rational_ints)
        if isinstance(similar_bound, Judgment):
            similar_bound = similar_bound.expr
        if not isinstance(similar_bound, NumberOrderingRelation):
            raise TypeError("'similar_bound' should be a "
                            "NumberOrderingRelation")

        # Get the canonical forms and make sure they are 'similar'
        # (the same on the left side).
        canonical_form, inv_scale = (
                self._canonical_form_and_inv_scale_factor())
        other_canonical_form, other_inv_scale = (
                similar_bound._canonical_form_and_inv_scale_factor())
        if canonical_form.lhs != other_canonical_form.lhs:
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
            assert is_literal_rational(rhs_diff)
            if isinstance(rhs_diff, Neg):
                fails_strength_check = True
        if fails_strength_check:
            raise TypeError(
                    "'similar_bound' should be a stronger "
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
            denom, numer = literal_rational_ints(other_inv_scale)
            #   to 'self':
            numer_factor, denom_factor = literal_rational_ints(inv_scale)
            numer *= numer_factor
            denom *= denom_factor
            scale_factor = simplified_rational_expr(numer, denom)
            # Multiply both sides (distribution will be dealt with
            # automatically when we equate expression with the 
            # same canonical forms below).
            known_bound = known_bound.mult_left_both_sides(scale_factor)

            # Weaken as appropriate.
            if rhs_diff == zero:
                if isinstance(self, LessEq) and (
                        isinstance(similar_bound, Less)):
                    known_bound = known_bound.derive_relaxed()
            else:
                rhs_diff_numer, rhs_diff_denom = literal_rational_ints(
                        rhs_diff)
                # scale the rhs diff from the canonical scaling to
                # the desired scaling.
                scaled_rhs_diff = simplified_rational_expr(
                        rhs_diff_numer*numer_factor,
                        rhs_diff_denom*denom_factor)
                assert not isinstance(scaled_rhs_diff, Neg)
                if known_bound.is_reversed():
                    # a > x => a + c > x   with c > 0
                    known_bound = known_bound.add_left(scaled_rhs_diff)
                else:
                    # x < a => x < a + c   with c > 0
                    known_bound = known_bound.add_right(scaled_rhs_diff)
            
            # See if we need to add something terms to both sides,
            # making replacements to the desired form.
            lhs_diff = subtract(self.normal_lhs, known_bound.normal_lhs)
            lhs_diff = lhs_diff.simplified()
            if lhs_diff.canonical_form() != zero:
                # Replacements will be used to get the expression
                # in the desired form.
                replacements = []
                replacements.append(
                        Equals(self.normal_lhs,
                               Add(known_bound.normal_lhs, lhs_diff)))
                replacements.append(
                        Equals(self.normal_rhs,
                               Add(known_bound.normal_rhs, lhs_diff)))
                # Check and prove the replacments.
                for _k, replacement in enumerate(replacements):
                    assert (replacement.lhs.canonical_form() == 
                            replacement.rhs.canonical_form())
                    replacements[_k] = replacement.prove()
                # Add to both sides.
                known_bound = known_bound.add_right_both_sides(
                        lhs_diff, replacements=replacements)
            else:
                # Both sides should already be equal (with the same
                # canonical forms).  Make the substitutions.
                assert (self.normal_lhs.canonical_form() == 
                        known_bound.normal_lhs.canonical_form())
                assert (self.normal_rhs.canonical_form() == 
                        known_bound.normal_rhs.canonical_form())
                known_bound = known_bound.inner_expr.normal_lhs.substitue(
                        self.normal_lhs)
                known_bound = known_bound.inner_expr.normal_rhs.substitue(
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
        
    def _canonical_form_and_inv_scale_factor(self):
        '''
        Returns the canonical form and the inverse scale factor used in 
        obtaining the canonical form.  Helper function for
        canonical_form.
        '''
        from proveit.numbers import (zero, one, Add, Neg, Mult, Div, 
                                     is_literal_rational)
        # Obtain the canonical forms of both sides.
        canonical_lhs = self.normal_lhs.canonical_form()
        canonical_rhs = self.normal_rhs.canonical_form()
        # Extract the literal, rational (constant) terms to add to
        # both sides to move the constant to the right side.
        constant_terms = []
        for side, sign in zip((canonical_lhs, canonical_rhs), (-1, 1)):
            if isinstance(side, Add):
                for term in side.terms:
                    if is_literal_rational(term):
                        if sign < 1:
                            term = Neg(term).canonical_form()
                        constant_terms.append(term)
        # lhs: original_lhs - original_rhs + constants
        # rhs: constants
        lhs = Add(self.normal_lhs, Neg(self.normal_rhs), *constant_terms)
        lhs = lhs.canonical_form()
        rhs = Add(*constant_terms).canonical_form()
        
        if lhs == zero:
            # Special case involving only literal, rationals.
            if rhs == zero:
                # Relation with zero on both sides.
                return self.__class__(lhs, rhs), one
            # Relation between zero and one.
            return self.__class__(zero, one), rhs
        
        # Now deterministically scale both sides.
        inv_scale_factor = one
        if isinstance(lhs, Add):
            # Choose the first term to normalize according.
            term = next(iter(lhs.terms))
            if isinstance(term, Mult) and (
                    is_literal_rational(term.factors[0])):
                # Term with rational coefficient.
                inv_scale_factor = term.factors[0]
            else:
                # Term with no rational coefficient.
                inv_scale_factor = one # No need to rescale
        elif isinstance(lhs, Mult) and is_literal_rational(lhs.factors[0]):
            # Scale inversely by the one and only coefficient.
            inv_scale_factor = lhs.factors[0]        
        if inv_scale_factor != one:
            # Rescale
            lhs = Div(lhs, inv_scale_factor).canonical_form()
            rhs = Div(rhs, inv_scale_factor).canonical_form()
        
        # Return the expression indicating that the
        # sum of terms is less than (or equal) to a literal rational.
        return self.__class__(lhs, rhs), inv_scale_factor
    
    def _deduce_equality(self, equality):
        '''
        Prove that this NumberOrderingRelation is equal an expression 
        that has the same canonical form.  Do this through mutual
        implication.
        '''
        from proveit.logic import Iff
        mutual_impl = Iff(equality.lhs, equality.rhs).conclude_by_definition()
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
