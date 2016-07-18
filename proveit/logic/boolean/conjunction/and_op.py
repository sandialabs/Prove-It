from proveit import Literal, AssociativeOperation
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.common import A, B, C

AND = Literal(__package__, stringFormat = 'and', latexFormat = r'\land')

class And(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        AssociativeOperation.__init__(self, AND, *operands)
        
    @classmethod
    def operatorOfOperation(subClass):
        return AND
    
    def deriveInPart(self, indexOrExpr):
        r'''
        From :math:`(A \land ... \land X \land ... \land Z)` derive :math:`X`.  indexOrExpr specifies 
        :math:`X` either by index or the expr.
        '''
        from axioms import andImpliesEach
        from proveit.common import Aetc, Cetc
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operands).index(indexOrExpr)
        return andImpliesEach.specialize({Aetc:self.operands[:idx], B:self.operands[idx], Cetc:self.operands[idx+1:]}).deriveConclusion()
    
    def deriveLeft(self):
        '''
        From (A and B), derive and return A.
        '''
        assert len(self.operands) == 2
        return self.deriveInPart(0)

    def deriveRight(self):
        '''
        From (A and B), derive and return B.
        '''
        assert len(self.operands) == 2
        return self.deriveInPart(1)
        
    def decompose(self):
        '''
        From (A and B), derive and return A, B as a tuple.
        '''        
        return (self.deriveLeft(), self.deriveRight())

    def concludeViaComposition(self):
        '''
        Prove and return some (A and B) assuming A, B.  See also the compose method to
        do this constructively.
        '''
        return compose(*self.operands)
            
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from axioms import andComposition, andTT, andTF, andFT, andFF
        if len(self.operands) >= 3:
            # A and B and ..C.. = A and (B and ..C..)
            compositionEquiv = andComposition.specialize({A:self.operands[0], B:self.operands[1], C:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return andTT
            elif A == TRUE and B == FALSE: return andTF
            elif A == FALSE and B == TRUE: return andFT
            elif A == FALSE and B == FALSE: return andFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'and' expression is in the set of BOOLEANS.
        '''
        from theorems import conjunctionClosure
        if len(self.operands) > 2:
            raise Exception('Deducing more than binary conjunction in booleans has not been implemented')
        inBools = {deduceInBool(operand) for operand in self.operands}
        return conjunctionClosure.specialize({A:self.operands[0], B:self.operands[1]})
    
def compose(*expressions):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    from axioms import andComposition
    from theorems import conjunctionIntro
    from proveit.logic.boolean import deriveStmtEqTrue
    if len(expressions) == 2:
        exprA, exprB = expressions
        return conjunctionIntro.specialize({A:exprA, B:exprB})
    else:
        assert len(expressions) > 2, "Compose 2 or more expressions, but not less than 2."
        rightComposition = compose(*expressions[1:])
        # A and (B and ..C..) = TRUE, given A, B, ..C..
        nestedAndEqT = deriveStmtEqTrue(compose(expressions[0], rightComposition))
        # A and B and ..C.. = A and (B and ..C..)
        compositionEquality = andComposition.specialize({A:expressions[0], B:rightComposition.operands[0], C:rightComposition.operands[1:]})
        print nestedAndEqT
        print compositionEquality
        # [A and B and ..C..] given A, B, ..C..
        return compositionEquality.applyTransitivity(nestedAndEqT).deriveViaBooleanEquality()
    