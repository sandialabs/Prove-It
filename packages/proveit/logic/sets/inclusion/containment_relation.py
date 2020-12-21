from proveit import USE_DEFAULTS
from proveit.relation import (
    TransitiveRelation, TransitiveSequence, make_sequence_or_relation)

class ContainmentRelation(TransitiveRelation):
    r'''
    Base class for all strict and non-strict set containment
    relations.  Do not construct an object of this class directly!  
    Instead, use Subset, SubsetEq, Superset, or SupersetEq.
    '''

    def __init__(self, operator, lhs, rhs):
        TransitiveRelation.__init__(self, operator, lhs, rhs)

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
                if other.lhs == self.rhs:
                    return other.sub_right_side_into(self, assumptions=assumptions)
                elif other.rhs == self.rhs:
                    return other.sub_left_side_into(self, assumptions=assumptions)



class ContainmentSequence(TransitiveSequence):
    r'''
    Base class for the containment relation sequences.  
    Do not construct an object of this class directly!  
    Instead, use SubsetSequence or SupersetSequence
    '''

    def __init__(self, operators, operands):
        TransitiveSequence.__init__(self, operators, operands)
