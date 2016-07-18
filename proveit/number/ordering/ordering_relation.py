from proveit import BinaryOperation, safeDummyVar
from proveit.logic import Equals
from proveit.common import x, y

class OrderingRelation(BinaryOperation):
    r'''
    Base class for all strict and non-strict inequalities.
    Do not construct an object of this class directly!  Instead, use LessThan, LessThanEquals etc.
    '''
    def __init__(self, operator,lhs, rhs):
        BinaryOperation.__init__(self,operator, lhs, rhs)
        self.lhs = lhs
        self.rhs = rhs

    def deriveReversed(self):
        '''
        From, e.g., x >= y derive y <= x etc.
        '''
        from less_than import LESSTHAN, LESSTHANEQUALS
        from greater_than import GREATERTHAN, GREATERTHANEQUALS
        from axioms import reverseGreaterThanEquals, reverseLessThanEquals, reverseGreaterThan, reverseLessThan
        if self.operator == LESSTHANEQUALS:
            return reverseLessThanEquals.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        elif self.operator == LESSTHAN:
            return reverseLessThan.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        elif self.operator == GREATERTHANEQUALS:
            return reverseGreaterThanEquals.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        elif self.operator == GREATERTHAN:
            return reverseGreaterThan.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})
        else:
            raise ValueError("Invalid instance of OrderingRelation!")
    def applyTransitivity(self, other):
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
        return self.transitivityImpl(other).deriveConclusion().checked({self, other})

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
