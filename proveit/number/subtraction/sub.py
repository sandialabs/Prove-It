from proveit import Literal, BinaryOperation
from proveit.logic import NotEquals
from proveit.number.sets import Naturals, NaturalsPos, Integers, Reals, Complexes, zero
from proveit.common import w, x, y, z, vEtc, wEtc, xEtc, yEtc, zEtc

SUBTRACT = Literal(__package__, r'-', r'-')

class Sub(BinaryOperation):
    def __init__(self, operandA, operandB):
        r'''
        Sub one number from another
        '''
        BinaryOperation.__init__(self, SUBTRACT, operandA, operandB)

    @classmethod
    def operatorOfOperation(subClass):
        return SUBTRACT
    
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.subtractRealClosure
        elif numberSet == Complexes:
            return theorems.subtractComplexClosure
        elif numberSet == Integers:
            return theorems.subtractIntClosure
        elif numberSet == Naturals:
            return theorems.subtractClosureNats
        elif numberSet == NaturalsPos:
            return theorems.subtractClosureNatsPos
            
    
    def _notEqZeroTheorem(self):
        from theorems import diffNotEqZero
        # Can derive (a - b) != 0 given a != b.
        # Derive a != b from b != a in case we have proven b != a instead of a != b.
        NotEquals(self.operands[1], self.operands[0]).deriveReversed()
        return diffNotEqZero
    
    def factor(self, theFactor, pull='left', groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a common factor from a subtraction, pulling it either to the "left" or "right".
        If there are multiple occurrences in any term, the first occurrence is used.  
        If groupFactor is True and theFactor is a product, it will be grouped together as a 
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from proveit.number.multiplication.theorems import distributeThroughSubtractRev
        from proveit.number import Mult
        dummyVar = self.safeDummyVar()
        eq = Equation()
        # commute both terms so that the factor is at the beginning
        factorEqLeft = self.operands[0].factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=assumptions)
        factorEqRight = self.operands[1].factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=assumptions)
        # substitute the factored terms
        eq.update(factorEqLeft.substitution(Sub(dummyVar, self.operands[1]), dummyVar)).checked(assumptions)
        eq.update(factorEqRight.substitution(Sub(factorEqLeft.rhs, dummyVar), dummyVar)).checked(assumptions)
        # perform distribution in reverse
        num = len(theFactor.operands) if isinstance(theFactor, Mult) else 1
        if pull == 'left':
            wEtcSub = theFactor.operands if isinstance(theFactor, Mult) else [theFactor]
            xSub = factorEqLeft.rhs.operands[num:]
            ySub = factorEqRight.rhs.operands[num:]
            zEtcSub = []
        elif pull == 'right':            
            wEtcSub = []
            xSub = factorEqLeft.rhs.operands[:-num]
            ySub = factorEqRight.rhs.operands[:-num]
            zEtcSub = theFactor.operands if isinstance(theFactor, Mult) else [theFactor]
        xSub = xSub[0] if len(xSub) == 1 else Mult(*xSub)
        ySub = ySub[0] if len(ySub) == 1 else Mult(*ySub)
        deduceInComplexes(wEtcSub + [xSub] + [ySub] + zEtcSub, assumptions)
        eq.update(distributeThroughSubtractRev.specialize({wEtc:wEtcSub, x:xSub, y:ySub, zEtc:zEtcSub}))
        if groupFactor and num > 1:
            if pull=='left':
                eq.update(eq.eqExpr.rhs.group(endIdx=num, assumptions=assumptions))
            elif pull=='right':
                eq.update(eq.eqExpr.rhs.group(startIdx=-num, assumptions=assumptions))                
        return eq.eqExpr.checked(assumptions)
    
    def convertToAdd(self, assumptions=frozenset()):
        '''
        Given (x - y) deduce and return (x - y) = (x + (-y)).
        Assumptions may be needed to deduce that the operands are in Complexes.
        '''
        from theorems import subtractAsAddNeg
        deduceInComplexes(self.operands, assumptions)
        return subtractAsAddNeg.specialize({x:self.operands[0], y:self.operands[1]}).checked(assumptions)

    def distribute(self, assumptions=frozenset()):
        '''
        Given something of the form (a + b + ...) - (x + y + ...), deduce and return
        (a + b + ...) - (x + y + ...) = a + b + ... + (-x) + (-y) + ....
        Assumptions may be needed to deduce that the operands are in Complexes.        
        '''
        # first deduce: (a + b + ...) - (x + y + ...)  = (a + b + ...) + (-x) + (-y) + ...
        from proveit.number import Add
        eqn = Equation()
        if isinstance(self.operands[1], Add):
            from theorems import distributeSubtraction
            deduceInComplexes(self.operands[0], assumptions)
            deduceInComplexes(self.operands[1].operands, assumptions)
            eqn.update(distributeSubtraction.specialize({x:self.operands[0], yEtc:self.operands[1].operands}).checked(assumptions))
        else:
            eqn.update(self.convertToAdd(assumptions))
        expr = eqn.eqExpr.rhs
        dummyVar = expr.safeDummyVar()
        # next try to simplify any of the negated terms
        negatedTerms = [term for term in expr.operands[1:]]
        for k, negatedTerm in enumerate(negatedTerms):
            try:
                negTermSimplification = negatedTerm.simplification(assumptions)
                eqn.update(negTermSimplification.substitution(Add(*(expr.terms[:k+1] + [dummyVar] + expr.terms[k+2:])), dummyVar)).checked(assumptions)
                expr = eqn.eqExpr.rhs
            except:
                pass # skip over 
        # ungroup the first part if it is a sum: (a + b + ...) + (-x) + (-y) + ... = a + b + ... + (-x) + (-y) + ...
        if isinstance(self.operands[0], Add):
            eqn.update(expr.applyTransitivity(expr.ungroup(0)).checked(assumptions))
        return eqn.eqExpr

    def cancel(self, assumptions=frozenset()):
        '''
        Attempt to cancel any term of a subtraction and return the resulting equivalence.
        The first term on the left that is the same as on the right will be canceled.
        Assumptions may be needed to deduce that the operands are in Complexes.        
        '''
        from theorems import subtractCancelElimSums, subtractCancelElimLeftSum, subtractCancelElimRightSum
        from theorems import subtractCancelTwoSums, subtractCancelLeftSum, subtractCancelRightSum
        from theorems import subtractCancelLeftSumSingleRight, subtractCancelLeftSumSingleLeft, subtractCancelRightSumSingleRight, subtractCancelRightSumSingleLeft 
        from theorems import subtractCancelComplete
        from proveit.number import Add, Neg
        dummy = self.safeDummyVar()
        eq = Equation()
        expr = self
        if self.operands[0] == self.operands[1]:
            # x - x = 0
            deduceInComplexes(self.operands[0], assumptions)
            return subtractCancelComplete.specialize({x:self.operands[0]}).checked(assumptions)
        if isinstance(expr.operands[0], Sub):
            eq.update(expr.operands[0].convertToAdd(assumptions=assumptions).substitution(Sub(dummy, expr.operands[1]), dummy))
            expr = eq.eqExpr.rhs
        if isinstance(expr.operands[1], Sub):
            eq.update(expr.operands[1].convertToAdd(assumptions=assumptions).substitution(Sub(expr.operands[0], dummy), dummy))
            expr = eq.eqExpr.rhs
        if isinstance(expr.operands[0], Add):
            if isinstance(expr.operands[1], Add):
                deduceInComplexes(expr.operands[0].operands, assumptions=assumptions)
                deduceInComplexes(expr.operands[1].operands, assumptions=assumptions)                
                foundOne = False
                for idx1 in xrange(len(expr.operands[0].operands)):
                    try:
                        idx2 = expr.operands[1].operands.index(expr.operands[0].operands[idx1])
                        foundOne = True
                        break
                    except:
                        pass
                if not foundOne:
                    raise Exception("No common term found")
                wSub = expr.operands[0].operands[idx1]
                try:
                    idx2 = expr.operands[1].operands.index(wSub)
                except:
                    raise Exception(str(wSub) + " not found in " + str(expr.operands[1]) + " for a subtraction cancel")
                if len(expr.operands[0].operands) == 2 and len(expr.operands[1].operands) == 2:
                    # special case where Add on both sides is eliminated
                    if idx1 > 0:
                        # commute the left
                        eq.update(expr.operands[0].commute(assumptions=assumptions).substitution(Sub(dummy, expr.operands[1]), dummy))
                        expr = eq.eqExpr.rhs
                    if idx2 > 0:
                        # commute the right
                        eq.update(expr.operands[1].commute(assumptions=assumptions).substitution(Sub(expr.operands[0], dummy), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[0].operands[0] == expr.operands[1].operands[0] # the form we were supposed to get to
                    eq.update(subtractCancelElimSums.specialize({x:expr.operands[0].operands[0], y:expr.operands[0].operands[1], z:expr.operands[1].operands[1]}))
                elif len(expr.operands[0].operands) == 2:
                    # special case where Add on the left is eliminated
                    if idx1 > 0:
                        # commute the left
                        eq.update(expr.operands[0].commute(assumptions=assumptions).substitution(Sub(dummy, expr.operands[1]), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[0].operands[0] == expr.operands[1].operands[idx2] # the form we were supposed to get to
                    wSub = expr.operands[0].operands[0]
                    xSub = expr.operands[0].operands[1]
                    ySub = expr.operands[1].operands[:idx2]
                    zSub = expr.operands[1].operands[idx2+1:]
                    eq.update(subtractCancelElimLeftSum.specialize({w:wSub, x:xSub, yEtc:ySub, zEtc:zSub}))
                elif len(expr.operands[1].operands) == 2:
                    # special case where Add on the right is eliminated
                    if idx2 > 0:
                        # commute the right
                        eq.update(expr.operands[1].commute(assumptions=assumptions).substitution(Sub(expr.operands[0], dummy), dummy))
                        expr = eq.eqExpr.rhs
                    assert expr.operands[1].operands[0] == expr.operands[0].operands[idx1] # the form we were supposed to get to
                    wSub = expr.operands[0].operands[:idx1]
                    xSub = expr.operands[0].operands[idx1]
                    ySub = expr.operands[0].operands[idx1+1:]
                    zSub = expr.operands[1].operands[1]
                    eq.update(subtractCancelElimRightSum.specialize({wEtc:wSub, x:xSub, yEtc:ySub, z:zSub}))
                else:
                    vSub = expr.operands[0].operands[:idx1]
                    xSub = expr.operands[0].operands[idx1+1:]
                    ySub = expr.operands[1].operands[:idx2]
                    zSub = expr.operands[1].operands[idx2+1:]
                    eq.update(subtractCancelTwoSums.specialize({vEtc:vSub, w:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions))
            else:
                deduceInComplexes(expr.operands[0].operands, assumptions=assumptions)
                deduceInComplexes(expr.operands[1], assumptions=assumptions)                
                ySub = expr.operands[1]
                try:
                    idx1 = expr.operands[0].operands.index(ySub)
                except:
                    raise Exception(str(ySub) + " not found in " + str(expr.operands[0]) + " for a subtraction cancel")                    
                if len(expr.operands[0].operands) == 2:
                    # only one term remains
                    if idx1 == 0:
                        eq.update(subtractCancelLeftSumSingleRight.specialize({y:ySub, x:expr.operands[0].operands[1]})).checked(assumptions)
                    else:
                        eq.update(subtractCancelLeftSumSingleLeft.specialize({y:ySub, x:expr.operands[0].operands[0]})).checked(assumptions)                        
                else:
                    xSub = expr.operands[0].operands[:idx1]
                    zSub = expr.operands[0].operands[idx1+1:]
                    eq.update(subtractCancelLeftSum.specialize({xEtc:xSub, y:ySub, zEtc:zSub}).checked(assumptions))
        else:
            deduceInComplexes(expr.operands[0], assumptions=assumptions)
            deduceInComplexes(expr.operands[1].operands, assumptions=assumptions)                
            ySub = expr.operands[0]
            try:
                idx2 = expr.operands[1].operands.index(ySub)
            except:
                raise Exception(str(ySub) + " not found in " + str(expr.operands[1]) + " for a subtraction cancel")                    
            if len(expr.operands[1].operands) == 2:
                # only one term remains
                if idx2 == 0:
                    eq.update(subtractCancelRightSumSingleRight.specialize({y:ySub, x:expr.operands[1].operands[1]})).checked(assumptions)
                else:
                    eq.update(subtractCancelRightSumSingleLeft.specialize({y:ySub, x:expr.operands[1].operands[0]})).checked(assumptions)                        
            else:
                xSub = expr.operands[1].operands[:idx2]
                zSub = expr.operands[1].operands[idx2+1:]
                eq.update(subtractCancelRightSum.specialize({xEtc:xSub, y:ySub, zEtc:zSub}).checked(assumptions))
        if isinstance(eq.eqExpr.rhs, Neg) and (isinstance(eq.eqExpr.rhs.operand, Neg) or eq.eqExpr.rhs.operand == zero):
            eq.update(eq.eqExpr.rhs.simplification(assumptions)) # take care of double negation or zero negation
        return eq.eqExpr

