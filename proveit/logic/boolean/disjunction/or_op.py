from proveit import Literal, AssociativeOperation, USE_DEFAULTS, ProofFailure
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.common import A, B, C, Aetc, Cetc

OR = Literal(__package__, stringFormat = 'or', latexFormat = r'\lor')

class Or(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Or together any number of operands: A or B or C
        '''
        AssociativeOperation.__init__(self, OR, *operands)

    def conclude(self, assumptions):
        '''
        Try to automatically conclude this disjunction via any of its constituents.
        That is, conclude some :math:`A \lor B \lor ... \lor Z` via and of
        :math:'A', :math:'B', ..., or :math:'Z'.
        '''
        for operand in self.operands:
            try:
                operand.prove(assumptions)
                return self.concludeViaExample(operand)
            except:
                pass
        raise ProofFailure(self, assumptions, 'Unable to automatically conclude disjunction; none of the constituents are automatically provable.')

    @classmethod
    def operatorOfOperation(subClass):
        return OR
    
    def deriveRightIfNotLeft(self, assumptions=USE_DEFAULTS):
        '''
        From (A or B) derive and return B assuming Not(A), inBool(B). 
        '''
        from theorems import orImpliesRightIfNotLeft
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return orImpliesRightIfNotLeft.specialize({A:leftOperand, B:rightOperand}, assumptions=assumptions).deriveConclusion(assumptions)

    def deriveLeftIfNotRight(self, assumptions=USE_DEFAULTS):
        '''
        From (A or B) derive and return A assuming inBool(A), Not(B).
        '''
        from theorems import orImpliesLeftIfNotRight
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return orImpliesLeftIfNotRight.specialize({A:leftOperand, B:rightOperand}, assumptions=assumptions).deriveConclusion(assumptions)
        
    def deriveCommonConclusion(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From (A or B) derive and return the provided conclusion C assuming A=>C, B=>C, A,B,C in BOOLEANS.
        '''
        from theorems import hypotheticalDisjunction
        from proveit.logic import Implies, compose
        # forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        leftImplConclusion = Implies(leftOperand, conclusion)
        rightImplConclusion = Implies(rightOperand, conclusion)
        # (A=>C and B=>C) assuming A=>C, B=>C
        compose(leftImplConclusion, rightImplConclusion)
        return hypotheticalDisjunction.specialize({A:leftOperand, B:rightOperand, C:conclusion}, assumptions=assumptions).deriveConclusion(assumptions).deriveConclusion(assumptions)
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from axioms import orComposition, orTT, orTF, orFT, orFF
        if len(self.operands) >= 3:
            # A or B or ..C.. = A or (B or ..C..)
            compositionEquiv = orComposition.specialize({A:self.operands[0], B:self.operands[1], C:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return orTT
            elif A == TRUE and B == FALSE: return orTF
            elif A == FALSE and B == TRUE: return orFT
            elif A == FALSE and B == FALSE: return orFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'or' expression is in the set of BOOLEANS.
        '''
        from theorems import disjunctionClosure
        return disjunctionClosure.specialize({Aetc:self.operands}, assumptions)
    
    def concludeViaExample(self, trueOperand):
        '''
        From one true operand, conclude that this 'or' expression is true.
        Requires all of the operands to be in the set of BOOLEANS.
        '''
        from theorems import orIfAny
        index = self.operands.index(trueOperand)
        return orIfAny.specialize({Aetc:self.operands[:index], B:self.operands[index], Cetc:self.operands[index+1:]})
