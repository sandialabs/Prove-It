from proveit import Literal, Operation, USE_DEFAULTS
from proveit.logic.boolean.booleans import inBool
from proveit._common_ import A, B

class And(Operation):
    # The operator of the And operation
    _operator_ = Literal(stringFormat='and', latexFormat=r'\land', context=__file__)
    
    def __init__(self, *operands):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        Operation.__init__(self, And._operator_, operands)
    
    def conclude(self, assumptions):
        '''
        Try to automatically conclude this conjunction via composing the constituents.
        That is, conclude some :math:`A \land B \and ... \land Z` via
        :math:'A', :math:'B', ..., :math:'Z' individually.
        '''
        from ._theorems_ import trueAndTrue
        if self == trueAndTrue.expr: return trueAndTrue # simple special case
        return self.concludeViaComposition(assumptions)
    
    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically.
        '''
        yield self.deriveInBool
        yield self.deriveParts

    def negationSideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for Not(A and B and .. and .. Z).
        '''
        yield self.deriveInBool # (A and B and ... and Z) in Booleans
        
    def inBoolSideEffects(self, knownTruth):
        '''
        From (A and B and .. and Z) in Booleans deduce (A in Booleans), (B in Booleans), ...
        (Z in Booleans).
        '''
        yield self.deducePartsInBool
 
    def deriveInBool(self, assumptions=USE_DEFAULTS):
        '''
        From (A and B and ... and Z) derive [(A and B and ... and Z) in Booleans].
        '''
        inBool(self).conclude(assumptions=assumptions)
    
    def deriveParts(self, assumptions=USE_DEFAULTS):
        r'''
        From (A and B and ... and Z)` derive each operand:
        A, B, ..., Z.
        '''
        for i in xrange(len(self.operands)):
            self.deriveInPart(i, assumptions)        
    
    def deriveInPart(self, indexOrExpr, assumptions=USE_DEFAULTS):
        r'''
        From (A and ... and X and ... and Z)` derive X.  indexOrExpr specifies 
        :math:`X` either by index or the expr.
        '''
        from ._theorems_ import anyFromAnd, leftFromAnd, rightFromAnd
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
    
    def deduceLeftInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce A in Booleans from (A and B) in Booleans.
        '''
        from _axioms_ import leftInBool
        if len(self.operands) == 2:
            leftInBool.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        
    def deduceRightInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce B in Booleans from (A and B) in Booleans.
        '''
        from _axioms_ import rightInBool
        if len(self.operands) == 2:
            rightInBool.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deducePartsInBool(self, indexOrExpr, assumptions=USE_DEFAULTS):
        '''
        Deduce A in Booleans, B in Booleans, ..., Z in Booleans
        from (A and B and ... and Z) in Booleans.
        '''
        for i in xrange(len(self.operands)):
            self.deducePartInBool(i, assumptions)        

    def deducePartInBool(self, indexOrExpr, assumptions=USE_DEFAULTS):
        '''
        Deduce X in Booleans from (A and B and .. and X and .. and Z) in Booleans
        provided X by expression or index number.
        '''
        from ._theorems_ import eachInBool
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operands).index(indexOrExpr)
        if idx < 0 or idx >= len(self.operands):
            raise IndexError("Operand out of range: " + str(idx))
        if len(self.operands)==2:
            if idx==0: self.deduceLeftInBool(assumptions)
            elif idx==1: self.deduceRightInBool(assumptions)
        return eachInBool.specialize({Amulti:self.operands[:idx], B:self.operands[idx], Cmulti:self.operands[idx+1:]}, assumptions=assumptions)
    
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from ._axioms_ import andTT, andTF, andFT, andFF # load in truth-table evaluations    
        from ._theorems_ import conjunctionTrueEval, conjunctionFalseEval
        from proveit.logic.boolean._common_ import TRUE, FALSE
        falseIndex = -1
        for i, operand in enumerate(self.operands):
            if operand != TRUE and operand != FALSE:
                # The operands are not all true/false, so try the default evaluate method
                # which will attempt to evaluate each of the operands.
                return Operation.evaluate(self, assumptions)
            if operand == FALSE:
                falseIndex = i
        if len(self.operands) == 2:
            # This will automatically return andTT, andTF, andFT, or andFF
            return Operation.evaluate(self, assumptions)
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
        from ._theorems_ import binaryCommutation, andCommutation
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
        from ._theorems_ import conjunctionClosure
        return conjunctionClosure.specialize({Amulti:self.operands}, assumptions=assumptions)
    
def compose(expressions, assumptions=USE_DEFAULTS):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    if len(expressions)==2:
        from ._theorems_ import andIfBoth
        return andIfBoth.specialize({A:expressions[0], B:expressions[1]}, assumptions=assumptions)
    else:
        from ._theorems_ import andIfAll
        return andIfAll.specialize({Amulti:expressions}, assumptions=assumptions)
