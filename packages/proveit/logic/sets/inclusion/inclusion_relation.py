from proveit import USE_DEFAULTS
from proveit.relation import (
    TransitiveRelation, total_ordering)


class InclusionRelation(TransitiveRelation):
    r'''
    Base class for all strict and non-strict set containment
    relations.  Do not construct an object of this class directly!
    Instead, use Subset, SubsetEq, Superset, or SupersetEq.
    '''

    def __init__(self, operator, lhs, rhs, *, styles):
        TransitiveRelation.__init__(self, operator, lhs, rhs,
                                    styles=styles)
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
    
    @staticmethod
    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        apply_transitivity(Subset(A,B), SetEquiv(B,C)) 
        returns Subset(A,C)
        '''
        from proveit.logic import Equals, SetEquiv, SubsetEq
        if isinstance(other, Equals):
            return TransitiveRelation.apply_transitivity(self, other,
                                                         assumptions)
        if isinstance(other, SetEquiv):
            # From set equivalence, derive the appropriate subset_eq
            # so we can use normal subset transitivity.
            if other.lhs == self.superset or other.rhs == self.subset:
                # EITHER (A subset B) and (B set_equiv C) 
                # OR (A subset B) and (C set_equiv A)
                other_as_subset_eq = SubsetEq(*other.operands.entries)
            elif other.rhs == self.superset or other.lhs == self.subset:
                # EITHER (A subset B) and (C set_equiv B)
                # OR (A subset B) and (A set_equiv C)
                other_as_subset_eq = SubsetEq(
                        *reversed(other.operands.entries))
            else:
                raise ValueError("Unable to apply transitivity between %s "
                                 "and %s."%(self, other))
            return self.apply_transitivity(other_as_subset_eq, assumptions)

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
