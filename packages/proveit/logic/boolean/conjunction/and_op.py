from proveit import Literal, AssociativeOperation, USE_DEFAULTS, tryDerivation
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.common import A, B, Amulti, Cmulti

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
        That is, deduce :math:'A', :math:'B', ..., :math:'Z' from
        :math:`A \land B \and ... \land Z`.
        '''
        if len(self.operands) == 2:
            tryDerivation(self.deriveLeft(assumptions=knownTruth.assumptions))
            tryDerivation(self.deriveRight(assumptions=knownTruth.assumptions))
        else:
            for i in xrange(len(self.operands)):
                tryDerivation(self.deriveInPart(i, assumptions=knownTruth.assumptions))
        
    def deriveInPart(self, indexOrExpr, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land ... \land X \land ... \land Z)` derive :math:`X`.  indexOrExpr specifies 
        :math:`X` either by index or the expr.
        '''
        from _theorems_ import anyFromConjunction, leftFromConjunction, rightFromConjunction
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operands).index(indexOrExpr)
        if idx < 0 or idx >= len(self.operands):
            raise IndexError("Operand out of range: " + str(idx))
        if len(self.operands)==2:
            if idx==0:
                return leftFromConjunction.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
            elif idx==1:
                return rightFromConjunction.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        return anyFromConjunction.specialize({Amulti:self.operands[:idx], B:self.operands[idx], Cmulti:self.operands[idx+1:]}, assumptions=assumptions)
    
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
    from _theorems_ import binaryConjunctionIntro, conjunctionIntro
    if len(expressions)==2:
        return binaryConjunctionIntro.specialize({A:expressions[0], B:expressions[1]}, assumptions=assumptions)
    return conjunctionIntro.specialize({Amulti:expressions}, assumptions=assumptions)
