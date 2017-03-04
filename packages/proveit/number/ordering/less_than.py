from proveit import Literal, USE_DEFAULTS
from proveit.logic import Equals
from ordering_relation import OrderingRelation
from proveit.common import a, b, c, x, y, z

LESSTHAN = Literal(__package__, r'<', r'<')
LESSTHANEQUALS = Literal(__package__, r'<=', r'\leq')

class LesserRelation(OrderingRelation):
    # map left-hand-sides to KnownTruths of LesserRelations
    knownLeftSides = dict()    
    # map right-hand-sides to KnownTruths of LesserRelations
    knownRightSides = dict()    

    def __init__(self, operator, lhs, rhs):
        OrderingRelation.__init__(self, operator, lhs, rhs)

    def lower(self):
        '''
        Returns the lower bound side of this inequality.
        '''
        return self.lhs

    def upper(self):
        '''
        Returns the upper bound side of this inequality.
        '''
        return self.rhs
    
    def deriveSideEffects(self, knownTruth):
        '''
        Record the knownTruth in LesserRelation.knownLeftSides and 
        LesserRelation.knownRightSides.  This information may
        be useful for concluding new inequalities via transitvity.
        Also execute generic OrderingRelation side effects.
        '''
        LesserRelation.knownLeftSides.setdefault(self.lhs, set()).add(knownTruth)
        LesserRelation.knownLeftSides.setdefault(self.rhs, set()).add(knownTruth)
        OrderingRelation.deriveSideEffects(self, knownTruth)
    

class LessThan(LesserRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at bigger than first.
        '''
        OrderingRelation.__init__(self, LESSTHAN,lhs,rhs)
        
    @classmethod
    def operatorOfOperation(subClass):
        return LESSTHAN
            
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from greater_than import GreaterThan
        return GreaterThan(self.rhs, self.lhs)
        
    def deduceInBooleans(self, assumptions=frozenset()):
        from theorems import lessThanInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return lessThanInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)

    def deriveRelaxed(self, assumptions=frozenset()):
        '''
        Relax a < b to a <= b, deducing the latter from the former (self) and returning the latter.
        Assumptions may be required to deduce that a and b are in Reals.
        '''
        from theorems import relaxLessThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return relaxLessThan.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
        
    def transitivityImpl(self, other, assumptions=USE_DEFAULTS):
        from axioms import lessThanTransLessThanRight, lessThanTransLessThanEqualsRight
        from axioms import lessThanTransLessThanLeft, lessThanTransLessThanEqualsLeft
        from proveit.number import GreaterThan, GreaterThanEquals

        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,GreaterThan) or isinstance(other,GreaterThanEquals):
            other = other.deriveReversed(assumptions)
#            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.               
        if other.lhs == self.rhs:
            if isinstance(other,LessThan):
                result = lessThanTransLessThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent(assumptions)
                #print self,result
                return result.checked({self})
            elif isinstance(other,LessThanEquals):
                result = lessThanTransLessThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent(assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,LessThan):
                result = lessThanTransLessThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent(assumptions)
                return result
            elif isinstance(other,LessThanEquals):
                result = lessThanTransLessThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent(assumptions)
                return result
        else:
            raise ValueError("Cannot derive implication from input!")

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a < b`, derive and return :math:`-a > -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from theorems import negatedLessThan
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedLessThan.specialize({a:self.lhs, b:self.rhs})
        
    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a < b`, derive and return :math:`a + c < b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from theorems import lessThanAddRight, lessThanAddLeft, lessThanSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return lessThanSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return lessThanAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return lessThanAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))

class LessThanEquals(LesserRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at least as big as first.
        '''
        LesserRelation.__init__(self, LESSTHANEQUALS,lhs,rhs)
    
    @staticmethod
    def knownRelationsFromLeft(expr, assumptionsSet):
        '''
        Return the known relations involving the left side which is the lower
        side of the relation.
        '''
        return OrderingRelation.knownRelationsFromLower(expr, assumptionsSet)
                
    @staticmethod
    def knownRelationsFromRight(expr, assumptionsSet):
        '''
        Return the known relations involving the right side which is the upper
        side of the relation.
        '''
        return OrderingRelation.knownRelationsFromUpper(expr, assumptionsSet)
            
    def reversed(self):
        '''
        Returns the reversed inequality Expression.
        '''
        from greater_than import GreaterThanEquals
        return GreaterThanEquals(self.rhs, self.lhs)

    @classmethod
    def operatorOfOperation(subClass):
        return LESSTHANEQUALS
            
    def deduceInBooleans(self, assumptions=frozenset()):
        from theorems import lessThanEqualsInBools
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return lessThanEqualsInBools.specialize({a:self.lhs, b:self.rhs}).checked(assumptions)
    
    def unfold(self, assumptions=frozenset()):
        from axioms import lessThanEqualsDef
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return lessThanEqualsDef.specialize({x:self.lhs, y:self.rhs})
    
    def transitivityImpl(self, other, assumptions=USE_DEFAULTS):
        from axioms import lessThanEqualsTransLessThanRight, lessThanEqualsTransLessThanEqualsRight
        from axioms import lessThanEqualsTransLessThanLeft, lessThanEqualsTransLessThanEqualsLeft
        from proveit.number import GreaterThan, GreaterThanEquals
        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,GreaterThan) or isinstance(other,GreaterThanEquals):
            other = other.deriveReversed(assumptions)
        elif isinstance(other,Equals):
            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.               
        if other.lhs == self.rhs:
            if isinstance(other,LessThan):
                result = lessThanEqualsTransLessThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent(assumptions)
                return result.checked({self})
            elif isinstance(other,LessThanEquals):
                result = lessThanEqualsTransLessThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConsequent(assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,LessThan):
                result = lessThanEqualsTransLessThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent(assumptions)
                return result
            elif isinstance(other,LessThanEquals):
                result = lessThanEqualsTransLessThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConsequent(assumptions)
                return result
#           result = equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.rhs}).deriveConsequent()
        else:
            raise ValueError("Cannot derive implication from input!")

    def deriveNegated(self, assumptions=frozenset()):
        '''
        From :math:`a \leq b`, derive and return :math:`-a \geq -b`.
        Assumptions may be required to prove that a, and b are in Reals.        
        '''
        from theorems import negatedLessThanEquals
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        return negatedLessThanEquals.specialize({a:self.lhs, b:self.rhs})
    
    def deriveShifted(self, addend, addendSide='right', assumptions=frozenset()):
        r'''
        From :math:`a \leq b`, derive and return :math:`a + c \leq b + c` where c is the given shift.
        Assumptions may be required to prove that a, b, and c are in Reals.
        '''
        from theorems import lessThanEqualsAddRight, lessThanEqualsAddLeft, lessThanEqualsSubtract
        deduceInReals(self.lhs, assumptions)
        deduceInReals(self.rhs, assumptions)
        deduceInReals(addend, assumptions)
        if addendSide == 'right':
            '''
            # Do this later and get it to work properly with deriveAdded
            if isinstance(addend, Neg):
                deduceInReals(addend.operand, assumptions)
                return lessThanEqualsSubtract.specialize({a:self.lhs, b:self.rhs, c:addend.operand}).checked(assumptions)
            else:
            '''
            return lessThanEqualsAddRight.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        elif addendSide == 'left':
            return lessThanEqualsAddLeft.specialize({a:self.lhs, b:self.rhs, c:addend}).checked(assumptions)
        else:
            raise ValueError("Unrecognized addend side (should be 'left' or 'right'): " + str(addendSide))
        
