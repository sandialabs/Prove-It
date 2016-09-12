from proveit import Literal, BinaryOperation, USE_DEFAULTS
from equals import Equals
from proveit.common import x, y, A, X

NOTEQUALS = Literal(__package__, stringFormat = '!=', latexFormat = r'\neq')

class NotEquals(BinaryOperation):
    def __init__(self, a, b):
        BinaryOperation.__init__(self, NOTEQUALS, a, b)
        self.lhs = a
        self.rhs = b
        
    @classmethod
    def operatorOfOperation(subClass):
        return NOTEQUALS    
    
    def deriveSideEffects(self, knownTruth):
        '''
        Derive the reversed form, as a side effect.
        '''
        if (self.lhs != self.rhs):
            # automatically derive the reversed form which is equivalent
            self.deriveReversed(knownTruth.assumptions)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From x != y derive y != x.
        '''
        from theorems import notEqualsSymmetry
        return notEqualsSymmetry.specialize({x:self.lhs, y:self.rhs}).deriveConclusion(assumptions)

    def deriveViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        '''
        From A != FALSE, derive and return A assuming inBool(A).
        Also see version in Not class.
        '''
        from proveit.logic import FALSE, inBool
        from proveit.logic.boolean.theorems import fromNotFalse
        if self.rhs == FALSE:
            return fromNotFalse.specialize({A:self.lhs}).deriveConclusion(assumptions)

    def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form A != FALSE assuming A.
        Also see version in Not class.
        '''
        from proveit.logic import FALSE
        from proveit.logic.boolean.theorems import notEqualsFalse
        if self.rhs == FALSE:
            return notEqualsFalse.specialize({A:self.lhs}).deriveConclusion()

    def definition(self):
        '''
        Return (x != y) = Not(x=y) where self represents (x != y).
        '''
        from axioms import notEqualsDef
        return notEqualsDef.specialize({x:self.lhs, y:self.rhs})

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        from theorems import unfoldNotEquals
        return unfoldNotEquals.specialize({x:self.lhs, y:self.rhs}).deriveConclusion(assumptions)

    def evaluate(self):
        '''
        Given operands that may be evaluated, derive and return this
        expression equated to TRUE or FALSE.  If both sides equate to
        the same, it will equate to FALSE.  Otherwise, it calls
        evalEquality using the evaluated left and right hand sides
        of the expression to determine the evaluation of the equality.
        '''
        from proveit.logic.boolean.boolOps import _evaluate
        def doEval():
            '''
            Performs the actual work if we can't simply look up the evaluation.
            '''
            unfoldedEvaluation = self.unfold().evaluate()
            return self.definition().lhsSubstitute(Equals(X, unfoldedEvaluation.rhs), X)
        return _evaluate(self, doEval)    

    def deduceInBool(self):
        '''
        Deduce and return that this 'not equals' statement is in the set of BOOLEANS.
        '''
        from theorems import notEqualsInBool
        return notEqualsInBool.specialize({x:self.lhs, y:self.rhs})
