from proveit import Literal, Operation, maybeFencedString, maybeFencedLatex
from proveit.number.sets import Integers, Reals, Complexes, zero
from proveit._common_ import a, x, y

class Neg(Operation):
    # operator of the Neg operation.
    _operator_ = Literal(stringFormat='Neg', context=__file__)
    
    def __init__(self,A):
        Operation.__init__(self, Neg._operator_, A)
    
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Complexes:
            return theorems.negComplexClosure
        elif numberSet == Reals:
            return theorems.negRealClosure
        elif numberSet == Integers:
            return theorems.negIntClosure

    def _negativeTheorem(self):
        import theorems
        return theorems.negatedPositiveIsNegative

    def _positiveTheorem(self):
        import theorems
        return theorems.negatedNegativeIsPositive

    def _notEqZeroTheorem(self):
        import theorems
        return theorems.negNotEqZero
    
    def asInt(self):
        '''
        Convert a literal integer into a Python int.  This
        only works if the operand is a literal int.
        '''
        return -self.operand.asInt()    
    
    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, double negation or negating zero,
        derive and return this Neg expression equated with the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from theorems import negNeg, negZero
        
        if isinstance(self.operand, Neg):
            deduceInComplexes(self.operand.operand, assumptions)
            return negNeg.specialize({a:self.operand.operand}).checked(assumptions)
        elif self.operand == zero:
            return negZero
        raise ValueError('Only trivial simplification is implemented (double negation or negating zero)')
        
    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, double negation or negating zero,
        derive and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
    
    def string(self, **kwargs):
        return maybeFencedString('-'+self.operand.string(fence=True), **kwargs)

    def latex(self, **kwargs):
        return maybeFencedLatex('-'+self.operand.latex(fence=True), **kwargs)

    def distribute(self, assumptions=frozenset()):
        '''
        Distribute negation through a sum.
        '''
        from theorems import distributeNegThroughSum, distributeNegThroughSubtract
        from proveit.number import Add, Sub
        if isinstance(self.operand, Add):
            deduceInComplexes(self.operand.operands, assumptions)
            # distribute the negation over the sum
            eqn = Equation(distributeNegThroughSum.specialize({xEtc:self.operand.operands}))
            # try to simplify each term
            expr = eqn.eqExpr.rhs
            dummyVar = self.safeDummyVar()
            negatedTerms = [term for term in expr.operands]
            for k, negatedTerm in enumerate(negatedTerms):
                try:
                    negTermSimplification = negatedTerm.simplification(assumptions)
                    eqn.update(negTermSimplification.substitution(Add(*(expr.terms[:k] + [dummyVar] + expr.terms[k+1:])), dummyVar)).checked(assumptions)
                    expr = eqn.eqExpr.rhs
                except:
                    pass # skip over                     
            return eqn.eqExpr.checked(assumptions)
        elif isinstance(self.operand, Sub):
            deduceInComplexes(self.operand.operands, assumptions)
            return distributeNegThroughSubtract.specialize({x:self.operand.operands[0], y:self.operand.operands[1]}).checked(assumptions)
        else:
            raise Exception('Only negation distribution through a sum or subtract is implemented')

    def factor(self,operand,pull="left", groupFactor=None, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a factor from a negated expression, pulling it either to the "left" or "right".
        groupFactor and groupRemainder are not relevant but kept for compatibility with 
        other factor methods.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        FACTORING FROM NEGATION FROM A SUM NOT IMPLEMENTED YET.
        '''
        from theorems import negTimesPosRev, posTimesNegRev
        if isinstance(operand, Neg):
            if pull == 'left':
                thm = negTimesPosRev
            else:
                thm = posTimesNegRev
            operand = operand.operand
        else:
            if pull == 'left':
                thm = posTimesNegRev
            else:
                thm = negTimesPosRev
        operandFactorEqn = self.operand.factor(operand, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
        # in this instance, the automated way is safe because there is no other operand:
        eqn1 = operandFactorEqn.substitution(self) 
        deduceInComplexes(operandFactorEqn.rhs.operands, assumptions)
        eqn2 = thm.specialize({x:operandFactorEqn.rhs.operands[0], y:operandFactorEqn.rhs.operands[1]})
        return eqn1.applyTransitivity(eqn2)
        

