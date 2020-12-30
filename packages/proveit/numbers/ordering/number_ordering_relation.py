from proveit.defaults import USE_DEFAULTS
from proveit.relation import TransitiveRelation, total_ordering


class NumberOrderingRelation(TransitiveRelation):
    def __init__(self, operator, lhs, rhs):
        TransitiveRelation.__init__(self, operator, lhs, rhs)
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
        yield self.derive_reversed
    
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
        return new_rel.with_matching_style(self)

    def square_both_sides(self, *, simplify=True, assumptions=USE_DEFAULTS):
        from proveit.numbers import two
        # Match style (e.g., use '>' if 'direction' is 'reversed').
        new_rel = self.exponentiate_both_sides(two, simplify=simplify,
                                               assumptions=assumptions)
        # Match style (e.g., use '>' if 'direction' is 'reversed').
        return new_rel.with_matching_style(self)
        

    def square_root_both_sides(self, *, simplify=True,
                               assumptions=USE_DEFAULTS):
        from proveit.numbers import frac, one, two, Exp
        new_rel = self.exponentiate_both_sides(frac(one, two),
                                               simplify=simplify,
                                               assumptions=assumptions)
        if (isinstance(new_rel.lhs, Exp)
                and new_rel.lhs.exponent == frac(one, two)):
            new_rel = new_rel.inner_expr().lhs.with_styles(exponent='radical')
        if (isinstance(new_rel.rhs, Exp)
                and new_rel.rhs.exponent == frac(one, two)):
            new_rel = new_rel.inner_expr().rhs.with_styles(exponent='radical')
        # Match style (e.g., use '>' if 'direction' is 'reversed').
        return new_rel.with_matching_style(self)


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
