from proveit import (as_expression, Literal, Operation, safe_dummy_var,
                     USE_DEFAULTS)
from proveit import A, B, C, x
from proveit import f, S
from .inclusion_relation import InclusionRelation

class ProperSubset(InclusionRelation):
    '''
    Class to represent proper subset relation, such as
    A proper_subset B, to represent the claim that any element in
    set A is also in set B, while B also has at least one element
    not in set A. Example usage: ProperSubset(A, B).
    Intended to replace the equivalent but more ambiguously-named
    Subset class.
    '''
    # operator of the Subset operation
    _operator_ = Literal(
        string_format='proper_subset',
        latex_format=r'\subset',
        theory=__file__)

    # map left-hand-sides to ProperSubset Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_left_sides = dict()
    # map right-hand-sides to ProperSubset Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_right_sides = dict()

    def __init__(self, A, B):
        '''
        Create the expression for (A proper_subset B).
        '''
        InclusionRelation.__init__(
            self, ProperSubset._operator_, A, B)

    @staticmethod
    def reversed_operator_str(format_type):
        '''
        Reversing proper_subset gives proper_superset.
        '''
        return r'\supset' if format_type == 'latex' else 'proper_superset'

    def remake_constructor(self):
        if self.is_reversed():
            # Use the 'proper_superset' function if it is reversed.
            return 'proper_superset'
        # Use the default.
        return Operation.remake_constructor(self)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        '''
        #print("Entering the ProperSubset.conclude() method!")                   # for testing; delete later
        pass
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A proper_subset B, derive and return
        (A subset_eq B) and (B set_not_equiv A)
        '''
        from . import unfold_proper_subset
        unfolded = unfold_proper_subset.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        return unfolded.inner_expr().operands[0].with_mimicked_style(self)
    
    def derive_relaxed(self, assumptions=USE_DEFAULTS):
        '''
        From ProperSubset(A, B), derive SubsetEq(A, B).
        '''
        from . import relax_proper_subset
        new_rel = relax_proper_subset.instantiate(
            {A: self.subset, B: self.superset}, assumptions=assumptions)
        new_rel.with_mimicked_style(self)
        return new_rel

    def derive_superset_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subset B and x in A, derive x in B.
        '''
        from . import superset_membership_from_proper_subset
        return superset_membership_from_proper_subset.instantiate(
            {A: self.subset, B: self.superset, x: element},
            assumptions=assumptions)

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this ProperSubset(A, B)
        expression and something of the form SubsetEq(B, C),
        ProperSubset(B, C), or B=C, to obtain ProperSubset(A, C) as
        appropriate.
        '''
        from proveit.logic import Equals, SetEquiv, SubsetEq
        from . import (
            transitivity_subset_subset, transitivity_subset_eq_subset,
            transitivity_subset_subset_eq,)
        if isinstance(other, Equals) or isinstance(other, SetEquiv):
            return InclusionRelation.apply_transitivity(
                self, other, assumptions=assumptions)
        if other.subset == self.superset:
            if isinstance(other, ProperSubset):
                new_rel = transitivity_subset_subset.instantiate(
                    {A: self.subset, B: self.superset, C: other.superset},
                    assumptions=assumptions)
            elif isinstance(other, SubsetEq):
                new_rel = transitivity_subset_subset_eq.instantiate(
                    {A: self.subset, B: self.superset, C: other.superset},
                    assumptions=assumptions)
        elif other.superset == self.subset:
            if isinstance(other, ProperSubset):
                new_rel = transitivity_subset_subset.instantiate(
                    {A: other.subset, B: other.superset, C: self.superset},
                    assumptions=assumptions)
            elif isinstance(other, SubsetEq):
                new_rel = transitivity_subset_eq_subset.instantiate(
                    {A: other.subset, B: other.superset, C: self.superset},
                    assumptions=assumptions)
        else:
            raise ValueError(
                "Cannot perform transitivity with {0} and {1}!".
                format(self, other))
        return new_rel.with_mimicked_style(self)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this ProperSubset expression
        is in the Boolean set.
        '''
        from . import proper_subset_is_bool
        is_bool_stmt = proper_subset_is_bool.instantiate(
                {A: self.normal_lhs, B: self.normal_rhs}, 
                assumptions=assumptions)
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

# Provide aliases for ProperSubset to augment user's ease-of-use
SubsetProper = ProperSubset
StrictSubset = ProperSubset

def proper_superset(A, B):
    '''
    Return the expression representing (A superset B), internally
    represented as (B subset A) but with a style that reverses
    the direction.
    '''
    return ProperSubset(B, A).with_styles(direction = 'reversed')
