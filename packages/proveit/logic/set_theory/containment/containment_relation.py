from proveit import USE_DEFAULTS
from proveit.relation import (
    TransitiveRelation, TransitiveSequence, makeSequenceOrRelation)

class ContainmentRelation(TransitiveRelation):
    r'''
    Base class for all strict and non-strict set containment
    relations.  Do not construct an object of this class directly!  
    Instead, use Subset, SubsetEq, Superset, or SupersetEq.
    '''

    def __init__(self, operator, lhs, rhs):
        TransitiveRelation.__init__(self, operator, lhs, rhs)

    def sideEffects(self, knownTruth):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt deriveRelaxed (if applicable) and deriveReversed.
        '''
        for sideEffect in TransitiveRelation.sideEffects(self, knownTruth):
            yield sideEffect
        if hasattr(self, 'deriveRelaxed'):
            yield self.deriveRelaxed
        yield self.deriveReversed

    @staticmethod
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        applyTransitivity(Subset(A,B), Equals(B,C)) returns Subset(A,C)
        '''
        from proveit.logic import Equals
        if isinstance(other, Equals):
            if (self.proven(assumptions=assumptions) and
                other.proven(assumptions=assumptions)):
                if other.lhs == self.rhs:
                    return other.subRightSideInto(self, assumptions=assumptions)
                elif other.rhs == self.rhs:
                    return other.subLeftSideInto(self, assumptions=assumptions)



class ContainmentSequence(TransitiveSequence):
    r'''
    Base class for the containment relation sequences.  
    Do not construct an object of this class directly!  
    Instead, use SubsetSequence or SupersetSequence
    '''

    def __init__(self, operators, operands):
        TransitiveSequence.__init__(self, operators, operands)
