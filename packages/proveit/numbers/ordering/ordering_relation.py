from proveit.relation import TransitiveRelation, TransitiveSequence, make_sequence_or_relation

class OrderingRelation(TransitiveRelation):
    r'''
    Base class for all strict and non-strict inequalities.
    Do not construct an object of this class directly!  Instead, use LessThan, LessThanEquals etc.
    '''
    
    def __init__(self, operator,lhs, rhs):
        TransitiveRelation.__init__(self,operator, lhs, rhs)
    
    def side_effects(self, judgment):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt derive_negated, derive_relaxed (if applicable),
        and derive_reversed.
        '''
        for side_effect in TransitiveRelation.side_effects(self, judgment):
            yield side_effect
        #yield self.derive_negated # Needs to be implemented (again)
        if hasattr(self, 'derive_relaxed'):
            yield self.derive_relaxed
        yield self.derive_reversed
    
    def derive_shifted(self, addend, addend_side='right', assumptions=frozenset()):
        raise NotImplementedError('derive_shifted is implemented for each specific OrderingRelation')

    def derive_added(self, other_ordering_relation, assumptions=frozenset()):
        r'''
        Add this ordering relation with another ordering relation.
        For example, if self is (a < b) and other_ordering_relation is (c < d), then
        this derives and returns (a + c < b + d).
        '''
        from proveit.numbers import LessThan, LessThanEquals
        other = other_ordering_relation
        if not (isinstance(other, OrderingRelation)):
            raise ValueError("Expecting 'other_ordering_relation' to be an OrderingRelation")
        if (isinstance(self, LessThan) or isinstance(self, LessThanEquals)) != (isinstance(other, LessThan) or isinstance(other, LessThanEquals)):
            # reverse other to be consistent with self (both less than type or greater than type)
            other = other.derive_reversed()
        shifted_self = self.derive_shifted(other.lhs, 'right', assumptions) # e.g., a + c < b + c
        shifted_other = other.derive_shifted(self.rhs, 'left', assumptions) # e.g., b + c < b + d
        return shifted_self.apply_transitivity(shifted_other) # e.g., a + c < b + d

class OrderingSequence(TransitiveSequence):
    r'''
    Base class for the containment relation sequences.  
    Do not construct an object of this class directly!  
    Instead, use LesserSequence or GreaterSequence
    '''

    def __init__(self, operators, operands):
        TransitiveSequence.__init__(self, operators, operands)
