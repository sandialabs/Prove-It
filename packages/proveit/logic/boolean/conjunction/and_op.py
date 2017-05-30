from proveit import Literal, AssociativeOperation, USE_DEFAULTS, tryDerivation
from proveit.logic.boolean.booleans import TRUE, FALSE, inBool
from proveit.common import A, B, Amulti, Bmulti, Cmulti, Dmulti, Emulti

class And(AssociativeOperation):
    # The operator of the And operation
    _operator_ = Literal(stringFormat='and', latexFormat=r'\land', context=__file__)
    
    def __init__(self, *operands):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        AssociativeOperation.__init__(self, And._operator_, *operands)
    
    def conclude(self, assumptions):
        '''
        Try to automatically conclude this conjunction via composing the constituents.
        That is, conclude some :math:`A \land B \and ... \land Z` via
        :math:'A', :math:'B', ..., :math:'Z' individually.
        '''
        from _theorems_ import trueAndTrue
        if self == trueAndTrue.expr: return trueAndTrue # simple special case
        return self.concludeViaComposition(assumptions)
    
    def deriveSideEffects(self, knownTruth):
        '''
        From a conjunction, automatically derive the individual constituents.
        That is, deduce A, B, ..., Z from (A and B and ... and Z).
        Also derive that this conjunction is in the set of Booleans
        (which then propogates to its constituents being in the set of Booleans).
        '''
        tryDerivation(inBool(self).conclude, assumptions=knownTruth.assumptions)
        if len(self.operands) == 2:
            tryDerivation(self.deriveLeft, knownTruth.assumptions)
            tryDerivation(self.deriveRight, knownTruth.assumptions)
        else:
            for i in xrange(len(self.operands)):
                tryDerivation(self.deriveInPart, i, knownTruth.assumptions)
    
    def deduceNegationSideEffects(self, knownTruth):
        '''
        From not(A and B and ... and Z), automatically deduce that the
        conjunction is in the set of Booleans.
        '''
        tryDerivation(inBool(self).conclude, assumptions=knownTruth.assumptions)
    
    def deduceInBoolSideEffects(self, knownTruth):
        '''
        From (A and B) in Booleans deduce A in Booleans and B in Booleans, where self is (A and B).
        '''
        from _axioms_ import leftInBool, rightInBool
        from _theorems_ import eachInBool
        if len(self.operands) == 2:
            leftInBool.specialize({A:self.operands[0], B:self.operands[1]}, knownTruth.assumptions)
            rightInBool.specialize({A:self.operands[0], B:self.operands[1]}, knownTruth.assumptions)
        else:
            for k, operand in enumerate(self.operands):
                eachInBool.specialize({Amulti:self.operands[:k], B:operand, Cmulti:self.operands[k+1:]})

    def deriveInPart(self, indexOrExpr, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land ... \land X \land ... \land Z)` derive :math:`X`.  indexOrExpr specifies 
        :math:`X` either by index or the expr.
        '''
        from _theorems_ import anyFromAnd, leftFromAnd, rightFromAnd
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operands).index(indexOrExpr)
        if idx < 0 or idx >= len(self.operands):
            raise IndexError("Operand out of range: " + str(idx))
        if len(self.operands)==2:
            if idx==0:
                return leftFromAnd.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
            elif idx==1:
                return rightFromAnd.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        return anyFromAnd.specialize({Amulti:self.operands[:idx], B:self.operands[idx], Cmulti:self.operands[idx+1:]}, assumptions=assumptions)
    
    def deriveLeft(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land B)` derive :math:`A`.
        '''
        if len(self.operands) != 2:
            raise Exception('deriveLeft only applicable for binary conjunction operations')
        return self.deriveInPart(0, assumptions)

    def deriveRight(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land B)` derive :math:`B`.
        '''
        if len(self.operands) != 2:
            raise Exception('deriveRight only applicable for binary conjunction operations')
        return self.deriveInPart(1, assumptions)
        
    def concludeViaComposition(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return some (A and B ... and ... Z) via A, B, ..., Z each proven individually.
        See also the compose method to do this constructively.
        '''
        return compose(self.operands, assumptions)
    
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from _axioms_ import andTT, andTF, andFT, andFF # load in truth-table evaluations    
        from _theorems_ import conjunctionTrueEval, conjunctionFalseEval
        falseIndex = -1
        for i, operand in enumerate(self.operands):
            if operand != TRUE and operand != FALSE:
                # The operands are not all true/false, so try the default evaluate method
                # which will attempt to evaluate each of the operands.
                return AssociativeOperation.evaluate(self, assumptions)
            if operand == FALSE:
                falseIndex = i
        if len(self.operands) == 2:
            # This will automatically return andTT, andTF, andFT, or andFF
            return AssociativeOperation.evaluate(self, assumptions)
        if falseIndex >= 0:
            # one operand is FALSE so the whole conjunction evaluates to FALSE.
            return conjunctionFalseEval.specialize({Amulti:self.operands[:falseIndex], Cmulti:self.operands[falseIndex+1:]})
        else:
            # no operand is FALSE so the whole disjunction evaluates to TRUE.
            return conjunctionTrueEval.specialize({Amulti:self.operands})
    
    def commute(self, startIdx1=None, endIdx1=None, startIdx2=None, endIdx2=None, assumptions=frozenset()):
        '''
        Commute self.operands[startIdx1:endIdx1] with self.operands[startIdx2:endIdx2].  
        The default, if no indices are provided, is to commute the first operand with the rest
        (convenient especially when there are just two operands).
        Derives and returns the new conjunction operation from the original.
        '''
        from _theorems_ import binaryCommutation, andCommutation
        if startIdx1 is None and endIdx1 is None and startIdx2 is None and endIdx2 is None:
            stattIdx1, endIdx1, startIdx2, endIdx2 = 0, 1, 1, None
        nOperands = len(self.operands)
        start1, stop1, _ = slice(startIdx1, endIdx1).indices(nOperands)
        start2, stop2, _ = slice(startIdx2, endIdx2).indices(nOperands)
        if start1  > start2:
            # swap 1 and 2 so that 1 comes first
            startIdx1, endIdx1, startIdx2, endIdx2 = startIdx2, endIdx2, startIdx1, endIdx2
            start1, stop1, start2, stop2 = start2, stop2, start1, stop1
        if len(self.operands)==2 and (start1,stop1,start2,stop2)==(0,1,1,2):
            return binaryCommutation.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        
        if stop1 > start2:
            raise ValueError("Cannot commute overlapping sets of operands")
        Asub = self.operands[:startIdx1] if startIdx1 is not None else []
        Bsub = self.operands[startIdx1:endIdx1]
        Csub = self.operands[endIdx1:startIdx2]
        Dsub = self.operands[startIdx2:endIdx2]
        Esub = self.operands[endIdx2:] if endIdx2 is not None else []
        return andCommutation.specialize({Amulti:Asub, Bmulti:Bsub, Cmulti:Csub, Dmulti:Dsub, Emulti:Esub}, assumptions=assumptions)
        
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'and' expression is in the set of BOOLEANS.
        '''
        from _theorems_ import conjunctionClosure
        return conjunctionClosure.specialize({Amulti:self.operands}, assumptions=assumptions)
    
def compose(expressions, assumptions=USE_DEFAULTS):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    from _theorems_ import andIfBoth, andIfAll
    if len(expressions)==2:
        return andIfBoth.specialize({A:expressions[0], B:expressions[1]}, assumptions=assumptions)
    return andIfAll.specialize({Amulti:expressions}, assumptions=assumptions)
