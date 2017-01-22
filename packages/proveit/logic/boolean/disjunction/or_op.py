from proveit import Literal, AssociativeOperation, USE_DEFAULTS, ProofFailure
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.common import A, B, C, Amulti, Cmulti

OR = Literal(__package__, stringFormat = 'or', latexFormat = r'\lor')

class Or(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Or together any number of operands: A or B or C
        '''
        AssociativeOperation.__init__(self, OR, *operands)

    @classmethod
    def operatorOfOperation(subClass):
        return OR

    def conclude(self, assumptions):
        '''
        Try to automatically conclude this disjunction.  If any of its
        operands have pre-existing proofs, it will be proven via the orIfAny
        theorem.  Otherwise, a reduction proof will be attempted 
        (evaluating the operands).
        '''
        from _theorems_ import trueOrTrue, trueOrFalse, falseOrTrue
        from _theorems_ import orIfBoth, orIfOnlyLeft, orIfOnlyRight
        if self in {trueOrTrue.expr, trueOrFalse.expr, falseOrTrue.expr}:
            # should be proven via one of the imported theorems as a simple special case
            return self.prove() 
        # Prove that the disjunction is true by proving that ANY of its operands is true.
        # In the first attempt, don't use automation to prove any of the operands so that
        # we don't waste time trying to prove operands when we already know one to be true
        for useAutomationForOperand in [False, True]:
            provenOperandIndices = []
            for k, operand in enumerate(self.operands):
                try:
                    operand.prove(assumptions, automation=useAutomationForOperand)
                    provenOperandIndices.append(k)
                    self.concludeViaExample(operand) # possible way to prove it
                except:
                    pass
            if len(self.operands) == 2 and len(provenOperandIndices) > 0:
                # One or both of the two operands were known to be true (without automation).
                # Try a possibly simpler proof than concludeViaExample. 
                try:
                    if len(provenOperandIndices)==2:
                        return orIfBoth.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
                    elif provenOperandIndices[0] == 0:
                        return orIfOnlyLeft.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
                    else:
                        return orIfOnlyRight.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
                except:
                    pass
            if len(provenOperandIndices) > 0:
                try:
                    # proven using concludeViaExample above (unless orIf[Any,Left,Right] was not a usable theorem,
                    # in which case this will fail and we can simply try the default below)
                    return self.prove(assumptions, automation=False)
                except:
                    # orIf[Any,Left,Right] must not have been a usable theorem; use the default below.
                    break
        # Use the default when orIfAny/orIfLeft/orIfRight is not a usable theorem 
        # or there are no pre-existing proofs for any of the operands.
        return AssociativeOperation.conclude(self, assumptions)
    
    def deriveRightIfNotLeft(self, assumptions=USE_DEFAULTS):
        '''
        From (A or B) derive and return B assuming Not(A), inBool(B). 
        '''
        from _theorems_ import orImpliesRightIfNotLeft
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return orImpliesRightIfNotLeft.specialize({A:leftOperand, B:rightOperand}, assumptions=assumptions).deriveConclusion(assumptions)

    def deriveLeftIfNotRight(self, assumptions=USE_DEFAULTS):
        '''
        From (A or B) derive and return A assuming inBool(A), Not(B).
        '''
        from _theorems_ import orImpliesLeftIfNotRight
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return orImpliesLeftIfNotRight.specialize({A:leftOperand, B:rightOperand}, assumptions=assumptions).deriveConclusion(assumptions)
        
    def deriveCommonConclusion(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From (A or B) derive and return the provided conclusion C assuming A=>C, B=>C, A,B,C in BOOLEANS.
        '''
        from _theorems_ import hypotheticalDisjunction
        from proveit.logic import Implies, compose
        # forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        leftImplConclusion = Implies(leftOperand, conclusion)
        rightImplConclusion = Implies(rightOperand, conclusion)
        # (A=>C and B=>C) assuming A=>C, B=>C
        compose([leftImplConclusion, rightImplConclusion], assumptions)
        return hypotheticalDisjunction.specialize({A:leftOperand, B:rightOperand, C:conclusion}, assumptions=assumptions).deriveConclusion(assumptions).deriveConclusion(assumptions)
        
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from _axioms_ import orTT, orTF, orFT, orFF # load in truth-table evaluations  
        from _theorems_ import disjunctionTrueEval, disjunctionFalseEval
        trueIndex = -1
        for i, operand in enumerate(self.operands):
            if operand != TRUE and operand != FALSE:
                # The operands are not always true/false, so try the default evaluate method
                # which will attempt to evaluate each of the operands.
                return AssociativeOperation.evaluate(self, assumptions)
            if operand == TRUE:
                trueIndex = i
        if len(self.operands) == 2:
            # This will automatically return orTT, orTF, orFT, or orFF
            return AssociativeOperation.evaluate(self, assumptions)
        if trueIndex >= 0:
            # one operand is TRUE so the whole disjunction evaluates to TRUE.
            return disjunctionTrueEval.specialize({Amulti:self.operands[:trueIndex], Cmulti:self.operands[trueIndex+1:]}, assumptions=assumptions)
        else:
            # no operand is TRUE so the whole disjunction evaluates to FALSE.
            return disjunctionFalseEval.specialize({Amulti:self.operands}, assumptions=assumptions)
            
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'or' expression is in the set of BOOLEANS.
        '''
        from _theorems_ import binaryClosure, closure
        if len(self.operands) == 2:
            return binaryClosure.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            return closure.specialize({Amulti:self.operands}, assumptions=assumptions)
        
    def concludeViaExample(self, trueOperand, assumptions=USE_DEFAULTS):
        '''
        From one true operand, conclude that this 'or' expression is true.
        Requires all of the operands to be in the set of BOOLEANS.
        '''
        from _theorems_ import orIfAny, orIfLeft, orIfRight
        index = self.operands.index(trueOperand)
        if len(self.operands) == 2:
            if index == 0:
                return orIfLeft.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
            elif index == 1:
                return orIfRight.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)                
        return orIfAny.specialize({Amulti:self.operands[:index], B:self.operands[index], Cmulti:self.operands[index+1:]}, assumptions=assumptions)
