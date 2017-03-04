from proveit import BinaryOperation, safeDummyVar, ProofFailure, USE_DEFAULTS
from proveit.logic import Equals
from proveit.common import x, y

class OrderingRelation(BinaryOperation):
    r'''
    Base class for all strict and non-strict inequalities.
    Do not construct an object of this class directly!  Instead, use LessThan, LessThanEquals etc.
    '''
    
    # map Expressions to sets KnownTruths of OrderingRelations that involve the Expression
    # as a lower or upper bound respectively
    knownLowerBounds = dict()    
    knownUpperBounds = dict()    
    
    def __init__(self, operator,lhs, rhs):
        BinaryOperation.__init__(self,operator, lhs, rhs)
        self.lhs = lhs
        self.rhs = rhs

    def deriveSideEffects(self, knownTruth):
        '''
        Automatically derive the reversed form as a side effect.
        '''
        if (self.lhs != self.rhs):
            # automatically derive the reversed equivalent form
            self.deriveReversed(knownTruth.assumptions)

    def conclude(self, assumptions):
        '''
        Try to conclude the OrderingRelation using other OrderingRelations
        or Equals that are known to be true via transitivity.
        For example, if a<b, b=c, and c<=d are known
        truths (under the given assumptions), we can conclude that a<d
        (under these assumptions).
        '''
        from proveit.logic import transitivitySearch
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        return transitivitySearch(self, assumptions)

    @classmethod
    def knownRelationsFromLeft(orderingClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, right-hand-side) pairs for < or <= relations,
        if the class is a LesserRelation, or for > or >= relations, if
        the class is a GreaterRelation, that involve the given expression
        on the left side and are known to be true under the given 
        assumptions.
        '''
        for knownTruth in orderingClass.knownLeftSides.get(expr, []):
            if knownTruth.isSufficient(assumptionsSet):
                yield (knownTruth, knownTruth.rhs)
        for (knownTruth, otherExpr) in  Equals.knownRelationsFromLeft(expr, assumptionsSet):
            yield (knownTruth, otherExpr)
                
    @classmethod
    def knownRelationsFromRight(orderingClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, left-hand-side) pairs for < or <= relations,
        if the class is a LesserRelation, or for > or >= relations, if
        the class is a GreaterRelation, that involve the given expression
        on the right side and are known to be true under the given 
        assumptions.
        '''
        for knownTruth in orderingClass.knownRightSides.get(expr, []):
            if knownTruth.isSufficient(assumptionsSet):
                yield (knownTruth, knownTruth.lhs)
        for (knownTruth, otherExpr) in  Equals.knownRelations(expr, assumptionsSet):
            yield (knownTruth, otherExpr)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From, e.g., x >= y derive y <= x etc.
        '''
        from less_than import LESSTHAN, LESSTHANEQUALS
        from greater_than import GREATERTHAN, GREATERTHANEQUALS
        from axioms import reverseGreaterThanEquals, reverseLessThanEquals, reverseGreaterThan, reverseLessThan
        if self.operator == LESSTHANEQUALS:
            return reverseLessThanEquals.specialize({x:self.lhs, y:self.rhs}).deriveConsequent(assumptions)
        elif self.operator == LESSTHAN:
            return reverseLessThan.specialize({x:self.lhs, y:self.rhs}).deriveConsequent(assumptions)
        elif self.operator == GREATERTHANEQUALS:
            return reverseGreaterThanEquals.specialize({x:self.lhs, y:self.rhs}).deriveConsequent(assumptions)
        elif self.operator == GREATERTHAN:
            return reverseGreaterThan.specialize({x:self.lhs, y:self.rhs}).deriveConsequent(assumptions)
        else:
            raise ValueError("Invalid instance of OrderingRelation!")
    
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        if isinstance(other,Equals):
            if other.lhs in (self.lhs, self.rhs):
                subrule = other.rhsSubstitute
                commonExpr = other.lhs
            elif other.rhs in (self.lhs, self.rhs):
                subrule = other.lhsSubstitute
                commonExpr = other.rhs
            else:
                raise ValueError("Equality does not involve either side of inequality!")
            X = safeDummyVar(self)
            if commonExpr == self.lhs:
                return subrule(self.operator.operationMaker([X,self.rhs]),X)
            elif commonExpr == self.rhs:
                return subrule(self.operator.operationMaker([self.lhs,X]),X)
#                    return other.rhsSubstitute(X,self.operator.operationMaker([X,self.rhs]))
#                else:
#                    return other.rhsSubstitute(X,
        return self.transitivityImpl(other).deriveConsequent(assumptions)
        
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
