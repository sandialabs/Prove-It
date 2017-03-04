from proveit import Literal, USE_DEFAULTS
from proveit.logic import Equals
from ordering_relation import OrderingRelation
from proveit.common import a, b, x, y, z

GREATERTHAN = Literal(__package__, r'>', r'>')
GREATERTHANEQUALS = Literal(__package__, r'>=', r'\geq')

class GreaterRelation(OrderingRelation):
    # map left-hand-sides to KnownTruths of GreaterRelation
    knownLeftSides = dict()    
    # map right-hand-sides to KnownTruths of GreaterRelation
    knownRightSides = dict()    

    def __init__(self, operator, lhs, rhs):
        OrderingRelation.__init__(self, operator, lhs, rhs)
    
    def lower(self):
        '''
        Returns the lower bound side of this inequality.
        '''
        return self.rhs

    def upper(self):
        '''
        Returns the upper bound side of this inequality.
        '''
        return self.lhs
    
    def deriveSideEffects(self, knownTruth):
        '''
        Record the knownTruth in GreaterRelation.knownLeftSides and 
        GreaterRelation.knownRightSides.  This information may
        be useful for concluding new inequalities via transitvity.
        Also execute generic OrderingRelation side effects.
        '''
        GreaterRelation.knownLeftSides.setdefault(self.lhs, set()).add(knownTruth)
        GreaterRelation.knownLeftSides.setdefault(self.rhs, set()).add(knownTruth)
        OrderingRelation.deriveSideEffects(self, knownTruth)

class GreaterThan(GreaterRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        OrderingRelation.__init__(self, GREATERTHAN,lhs,rhs)
        
    @classmethod
    def operatorOfOperation(subClass):
        return GREATERTHAN
            
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from less_than import LessThan
        return LessThan(self.rhs, self.lhs)
    
    def deduceInBooleans(self, assumptions=frozenset()):
        from theorems import greaterThanInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return greaterThanInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
    
    def deriveRelaxed(self, assumptions=frozenset()):
        '''
        Relax a > b to a >= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Reals.
        '''
        from theorems import relaxGreaterThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return relaxGreaterThan.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
        
    def transitivityImpl(self, other, assumptions=USE_DEFAULTS):
        from axioms import greaterThanTransGreaterThanRight, greaterThanTransGreaterThanEqualsRight
        from axioms import greaterThanTransGreaterThanLeft, greaterThanTransGreaterThanEqualsLeft
        from proveit.number import LessThan, LessThanEquals
        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,LessThan) or isinstance(other,LessThanEquals):
            other = other.deriveReversed(assumptions)
        elif isinstance(other,Equals):
            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.
        if other.lhs == self.rhs:
            if isinstance(other,GreaterThan):
                result = greaterThanTransGreaterThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent(assumptions)
                return result.checked({self})
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanTransGreaterThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent(assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,GreaterThan):
                result = greaterThanTransGreaterThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent(assumptions)
                return result
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanTransGreaterThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent(assumptions)
                return result
        else:
            raise ValueError("Cannot derive implication from input!")

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a > b`, derive and return :math:`-a < -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from theorems import negatedGreaterThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedGreaterThan.specialize({a:self.lhs, b:self.rhs})

    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a > b`, derive and return :math:`a + c > b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from theorems import greaterThanAddRight, greaterThanAddLeft, greaterThanSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return greaterThanSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return greaterThanAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return greaterThanAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))


class GreaterThanEquals(GreaterRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if first number is at least as big as second.
        '''
        GreaterRelation.__init__(self, GREATERTHANEQUALS,lhs,rhs)

    @classmethod
    def operatorOfOperation(subClass):
        return GREATERTHANEQUALS
    
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from less_than import LessThanEquals
        return LessThanEquals(self.rhs, self.lhs)
        
    @staticmethod
    def knownRelationsFromLeft(expr, assumptionsSet):
        '''
        Return the known relations involving the left side which is the upper
        side of the relation.
        '''
        return OrderingRelation.knownRelationsFromUpper(expr, assumptionsSet)
                
    @staticmethod
    def knownRelationsFromRight(expr, assumptionsSet):
        '''
        Return the known relations involving the right side which is the lower
        side of the relation.
        '''
        return OrderingRelation.knownRelationsFromLower(expr, assumptionsSet)        
                        
    def deduceInBooleans(self, assumptions=frozenset()):
        from theorems import greaterThanEqualsInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return greaterThanEqualsInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)

    def unfold(self, assumptions=frozenset()):
        from axioms import greaterThanEqualsDef
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return greaterThanEqualsDef.specialize({x:self.lhs, y:self.rhs})
    
    def transitivityImpl(self, other, assumptions=USE_DEFAULTS):
        from axioms import greaterThanEqualsTransGreaterThanRight, greaterThanEqualsTransGreaterThanEqualsRight
        from axioms import greaterThanEqualsTransGreaterThanLeft, greaterThanEqualsTransGreaterThanEqualsLeft
        from proveit.number import LessThan, LessThanEquals
        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,LessThan) or isinstance(other,LessThanEquals):
            other = other.deriveReversed(assumptions)
        elif isinstance(other,Equals):
            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.
        if other.lhs == self.rhs:
            if isinstance(other,GreaterThan):
                result = greaterThanEqualsTransGreaterThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent()
                return result.checked({self})
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanEqualsTransGreaterThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent()
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,GreaterThan):
                result = greaterThanEqualsTransGreaterThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent()
                return result
            elif isinstance(other,GreaterThanEquals):
                result = greaterThanEqualsTransGreaterThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent()
                return result
        else:
            raise ValueError("Cannot derive implication from input!")

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a \geq b`, derive and return :math:`-a \leq -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from theorems import negatedGreaterThanEquals
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedGreaterThanEquals.specialize({a:self.lhs, b:self.rhs})

    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a \geq b`, derive and return :math:`a + c \geq b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from theorems import greaterThanEqualsAddRight, greaterThanEqualsAddLeft, greaterThanEqualsSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return greaterThanEqualsSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return greaterThanEqualsAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return greaterThanEqualsAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))


