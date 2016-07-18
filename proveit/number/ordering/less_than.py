from proveit import Literal
from proveit.logic import Equals
from ordering_relation import OrderingRelation
from proveit.common import a, b, c, x, y, z

LESSTHAN = Literal(__package__, r'<', r'<')
LESSTHANEQUALS = Literal(__package__, r'<=', r'\leq')

class LessThan(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at bigger than first.
        '''
        OrderingRelation.__init__(self, LESSTHAN,lhs,rhs)
        
    @classmethod
    def operatorOfOperation(subClass):
        return LESSTHAN
            
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
        
    def transitivityImpl(self,other):
        from axioms import reverseGreaterThanEquals, reverseGreaterThan
        from axioms import lessThanTransLessThanRight, lessThanTransLessThanEqualsRight
        from axioms import lessThanTransLessThanLeft, lessThanTransLessThanEqualsLeft
        from proveit.number import GreaterThan, GreaterThanEquals

        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,GreaterThan) or isinstance(other,GreaterThanEquals):
            other = other.deriveReversed()
#            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.               
        if other.lhs == self.rhs:
            if isinstance(other,LessThan):
                result = lessThanTransLessThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                #print self,result
                return result.checked({self})
            elif isinstance(other,LessThanEquals):
                result = lessThanTransLessThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,LessThan):
                result = lessThanTransLessThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
            elif isinstance(other,LessThanEquals):
                result = lessThanTransLessThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
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

class LessThanEquals(OrderingRelation):
    def __init__(self, lhs, rhs):
        r'''
        See if second number is at least as big as first.
        '''
        OrderingRelation.__init__(self, LESSTHANEQUALS,lhs,rhs)
        
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
    
    def transitivityImpl(self,other):
        from axioms import reverseGreaterThanEquals, reverseGreaterThan
        from axioms import lessThanEqualsTransLessThanRight, lessThanEqualsTransLessThanEqualsRight
        from axioms import lessThanEqualsTransLessThanLeft, lessThanEqualsTransLessThanEqualsLeft
        from proveit.number import GreaterThan, GreaterThanEquals
        if (other.rhs == self.rhs and other.lhs == self.lhs) or (other.rhs == self.lhs and other.lhs == self.rhs):
            raise ValueError("Cannot use transitivity with no new expression!")
        elif (other.rhs == other.lhs):
            raise ValueError("Cannot use transitivity with trivially reflexive relation!")
        if isinstance(other,GreaterThan) or isinstance(other,GreaterThanEquals):
            other = other.deriveReversed()
        elif isinstance(other,Equals):
            raise ValueError("Blame KMR for not getting to this yet!")
#            if other.lhs == self.lhs:
#                return other.               
        if other.lhs == self.rhs:
            if isinstance(other,LessThan):
                result = lessThanEqualsTransLessThanRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result.checked({self})
            elif isinstance(other,LessThanEquals):
                result = lessThanEqualsTransLessThanEqualsRight.specialize({x:self.lhs, y:self.rhs, z:other.rhs}).deriveConclusion()
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,LessThan):
                result = lessThanEqualsTransLessThanLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
            elif isinstance(other,LessThanEquals):
                result = lessThanEqualsTransLessThanEqualsLeft.specialize({x:self.lhs, y:self.rhs, z:other.lhs}).deriveConclusion()
                return result
#           result = equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.rhs}).deriveConclusion()
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
        
