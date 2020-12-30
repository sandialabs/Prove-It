from proveit import USE_DEFAULTS
from proveit.relation import (
    TransitiveRelation, total_ordering)


class InclusionRelation(TransitiveRelation):
    r'''
    Base class for all strict and non-strict set containment
    relations.  Do not construct an object of this class directly!
    Instead, use Subset, SubsetEq, Superset, or SupersetEq.
    '''

    def __init__(self, operator, lhs, rhs):
        TransitiveRelation.__init__(self, operator, lhs, rhs)
        self.subset = self.operands[0]
        self.superset = self.operands[1]

    @staticmethod
    def WeakRelationClass():
        from .subset_eq import SubsetEq
        return SubsetEq

    @staticmethod
    def StrongRelationClass():
        from .proper_subset import ProperSubset
        return ProperSubset

    @staticmethod
    def EquivalenceClass():
        from proveit.logic.sets.equivalence import SetEquiv
        return SetEquiv
    
    def side_effects(self, judgment):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt derive_relaxed (if applicable) and derive_reversed.
        '''
        for side_effect in TransitiveRelation.side_effects(self, judgment):
            yield side_effect
        if hasattr(self, 'derive_relaxed'):
            yield self.derive_relaxed
        yield self.derive_reversed

    @staticmethod
    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        apply_transitivity(Subset(A,B), Equals(B,C)) returns Subset(A,C)
        '''
        from proveit.logic import Equals
        if isinstance(other, Equals):
            if (self.proven(assumptions=assumptions) and
                    other.proven(assumptions=assumptions)):
                if other.subset == self.superset:
                    return other.sub_right_side_into(
                        self, assumptions=assumptions)
                elif other.superset == self.subset:
                    return other.sub_left_side_into(
                        self, assumptions=assumptions)

def inclusion_ordering(*relations):
    '''
    Return a conjunction of set inclusion ordering relations
    with a total-ordering style; for example,
    A proper_subset B subset_eq C set_equiv D proper_subset E
    '''
    from proveit.logic.sets.equivalence import SetEquiv
    for relation in relations:
        if (not isinstance(relation, InclusionRelation) and
               not isinstance(relation, SetEquiv)):
            raise TypeError("For a set inclusion ordering expression, "
                            "all relations must be either InclusionRelation "
                            "or SetEquiv objects.")
    return total_ordering(*relations)
