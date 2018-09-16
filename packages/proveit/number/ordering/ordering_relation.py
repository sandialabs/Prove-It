from proveit.relation import TransitiveRelation, TransitiveSequence

class OrderingRelation(TransitiveRelation):
    r'''
    Base class for all strict and non-strict inequalities.
    Do not construct an object of this class directly!  Instead, use LessThan, LessThanEquals etc.
    '''
    
    def __init__(self, operator,lhs, rhs):
        TransitiveRelation.__init__(self,operator, lhs, rhs)
    
    def sideEffects(self, knownTruth):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt deriveNegated, deriveRelaxed (if applicable),
        and deriveReversed.
        '''
        for sideEffect in TransitiveRelation.sideEffects(self, knownTruth):
            yield sideEffect
        yield self.deriveNegated
        if hasattr(self, 'deriveRelaxed'):
            yield self.deriveRelaxed
        yield self.deriveReversed
    
    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        raise NotImplementedError('deriveShifted is implemented for each specific OrderingRelation')

    def deriveAdded(self, otherOrderingRelation, assumptions=frozenset()):
        r'''
        Add this ordering relation with another ordering relation.
        For example, if self is (a < b) and otherOrderingRelation is (c < d), then
        this derives and returns (a + c < b + d).
        '''
        from proveit.number import LessThan, LessThanEquals
        other = otherOrderingRelation
        if not (isinstance(other, OrderingRelation)):
            raise ValueError("Expecting 'otherOrderingRelation' to be an OrderingRelation")
        if (isinstance(self, LessThan) or isinstance(self, LessThanEquals)) != (isinstance(other, LessThan) or isinstance(other, LessThanEquals)):
            # reverse other to be consistent with self (both less than type or greater than type)
            other = other.deriveReversed()
        shiftedSelf = self.deriveShifted(other.lhs, 'right', assumptions) # e.g., a + c < b + c
        shiftedOther = other.deriveShifted(self.rhs, 'left', assumptions) # e.g., b + c < b + d
        return shiftedSelf.applyTransitivity(shiftedOther) # e.g., a + c < b + d

class OrderingSequence(TransitiveSequence):
    r'''
    Base class for the containment relation sequences.  
    Do not construct an object of this class directly!  
    Instead, use SubsetSequence or SupersetSequence
    '''

    def __init__(self, operators, operands):
        TransitiveSequence.__init__(self, operators, operands)
