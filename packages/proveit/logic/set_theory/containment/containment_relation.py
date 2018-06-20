from proveit.relation import TransitiveRelation, TransitiveSequence

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
        attempt deriveRelaxed (if applicable).
        '''
        for sideEffect in TransitiveRelation.sideEffects(self, knownTruth):
            yield sideEffect
        if hasattr(self, 'deriveRelaxed'):
            yield self.deriveRelaxed

class ContainmentSequence(TransitiveSequence):
    r'''
    Base class for the containment relation sequences.  
    Do not construct an object of this class directly!  
    Instead, use SubsetSequence or SupersetSequence
    '''

    def __init__(self, operators, operands):
        TransitiveSequence.__init__(self, operators, operands)
