from proveit._generic_ import TransitiveRelation

class ContainmentRelation(TransitiveRelation):
    r'''
    Base class for all strict and non-strict set containment
    relations.  Do not construct an object of this class directly!  
    Instead, use Subset, SubsetEq, Superset, or SupersetEq.
    '''

    def __init__(self, operator,lhs, rhs):
        TransitiveRelation.__init__(self,operator, lhs, rhs)

    def sideEffects(self, knownTruth):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt deriveRelaxed (if applicable).
        '''
        for sideEffect in TransitiveRelation.sideEffects(self, knownTruth):
            yield sideEffect
        if hasattr(self, 'deriveRelaxed'):
            yield self.deriveRelaxed