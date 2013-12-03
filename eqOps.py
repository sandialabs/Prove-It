from proveItCore import *
from genericOperations import *

equality = Context('EQUALITY')

# equality is an important core concept
EQUALS = equality.addLiteral('EQUALS')
NOTEQUALS = equality.addLiteral('NOTEQUALS')

class Equals(BinaryOperation):
    def __init__(self, a, b):
        BinaryOperation.__init__(self, EQUALS, a, b)
        self.lhs = a
        self.rhs = b

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '='
        else:
            return '<mo>=</mo>'

    def remake(self, operator, operands):
        if operator == EQUALS and len(operands) == 2:
            return Equals(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)
        
    def deriveReversed(self):
        '''
        From A = B derive B = A.
        '''
        from basicLogic import A, B, equalsSymmetry
        return equalsSymmetry.specialize({A:self.lhs, B:self.rhs}).deriveConclusion()
    
    def applyTransitivity(self, otherEquality):
        '''
        From A = B (self) and B = C (otherEquality) derive and return A = C.
        Also works more generally as long as there is a common side to the equations.
        '''
        from basicLogic import A, B, C, compose, equalsTransitivity
        if self.rhs == otherEquality.lhs:
            # from A = B and B = C, derive A = C
            compose(self, otherEquality)
            return equalsTransitivity.specialize({A:self.lhs, B:self.rhs, C:otherEquality.rhs}).deriveConclusion().deriveConclusion()
        elif self.lhs == otherEquality.lhs:
            # from B = A and B = C, derive A = C
            return self.deriveReversed().applyTransitivity(otherEquality)
        elif self.lhs == otherEquality.rhs:
            # from B = A and B = C, derive A = C
            return self.deriveReversed().applyTransitivity(otherEquality.deriveReversed())
        elif self.rhs == otherEquality.rhs:
            # from A = B and C = B, derive A = C
            return self.applyTransitivity(otherEquality.deriveReversed())
        
    def deriveFromBooleanEquality(self):
        '''
        From A = TRUE derive A, or from A = FALSE derive Not(A).
        Note, see deriveStatementEqTrue or Not.equateNegatedToFalse for the reverse process.
        '''
        from basicLogic import A, TRUE, FALSE
        if self.rhs == TRUE:
            from basicLogic import equalsTrueElim
            return equalsTrueElim.specialize({A:self.lhs}).deriveConclusion() # A
        elif self.rhs == FALSE:
            from basicLogic import notFromEqFalse
            return notFromEqFalse.specialize({A:self.lhs}).deriveConclusion() # Not(A)
    
    def deriveIsInSingleton(self):
        '''
        From A = B, derive A in {B}.
        '''
        from sets import singletonDef
        singletonDef.specialize({x:self.lhs, y:self.rhs}).deriveLeft()
        
    def deriveViaEquivalence(self):
        '''
        From A = B, derive B given A
        '''
        from basicLogic import X, substitute
        return substitute(self, Function(X, [X]))

    def implicationViaEquivalence(self):
        '''
        From A = B, derive A=>B
        '''
        from basicLogic import X, substitute, Implies
        substitute(self, Function(X, [X]))
        return Implies(self.lhs, self.rhs)
        
        
class NotEquals(BinaryOperation):
    def __init__(self, a, b):
        BinaryOperation.__init__(self, NOTEQUALS, a, b)
        self.lhs = a
        self.rhs = b
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '!='
        elif formatType == MATHML:
            return '<mo>&#x2260;</mo>'

    def remake(self, operator, operands):
        if operator == NOTEQUALS and len(operands) == 2:
            return NotEquals(operands[0], operands[1])
        else:
            return Operation.remake(self, operator, operands)
        
    def deriveReversed(self):
        '''
        From A != B derive B != A.
        '''
        from basicLogic import A, B, notEqualsSymmetry  
        return notEqualsSymmetry.specialize({A:self.lhs, B:self.rhs}).deriveConclusion()

    def deriveFromDoubleNegation(self):
        '''
        Derive and return A given self and IsBool(A) where self is A!=FALSE.
        Also see version in Not class.
        '''
        from basicLogic import A, FALSE, fromNotEqualFalse  
        if self.rhs == FALSE:
            return fromNotEqualFalse.specialize({A:self.lhs}).deriveConclusion() 

    def unravel(self):
        '''
        Derive and return A != B given self where self is Not(A=B).
        '''
        from basicLogic import A, B, unfoldNotEquals
        return unfoldNotEquals.specialize({A:self.lhs, B:self.rhs}).deriveConclusion()
