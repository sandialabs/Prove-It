from proveit import Literal, Operation, maybeFencedString, maybeFencedLatex, USE_DEFAULTS, ProofFailure
from proveit.logic import isIrreducibleValue
from proveit.number.sets import Integers, Reals, Complexes
from proveit._common_ import a, x, y

class Neg(Operation):
    # operator of the Neg operation.
    _operator_ = Literal(stringFormat='-', context=__file__)
    
    def __init__(self,A):
        Operation.__init__(self, Neg._operator_, A)
    
    def irreducibleValue(self):
        from proveit.number import zero
        return isIrreducibleValue(self.operand) and self.operand != zero
        
    def deduceInNumberSet(self, NumberSet, assumptions=USE_DEFAULTS):
        '''
        given a number set, attempt to prove that the given expression is in that
        number set using the appropriate closure theorem
        '''
        from ._theorems_ import intClosure, realClosure, complexClosure
        from proveit.logic import InSet
        if NumberSet == Integers:
            return intClosure.specialize({a:self.operand})
        elif NumberSet == Reals:
            return realClosure.specialize({a:self.operand})
        elif NumberSet == Complexes:
            return complexClosure.specialize({a:self.operand})
        else:
            raise ProofFailure(InSet(self, NumberSet), assumptions, "No negation closure theorem for set %s"%str(NumberSet))
    
    def simplification(self, assumptions=USE_DEFAULTS, automation=True, innerExpr=None, inPlace=False):
        '''
        Derive and return this negation expression equated with a simpler form.
        Deals with double negation specifically.
        '''
        from proveit.number import zero
        from proveit.logic import Equals
        from ._theorems_ import doubleNegation, negatedZero
        if isinstance(self.operand, Neg):
            # simplify double negation
            expr = doubleNegation.specialize({x:self.operand.operand}, assumptions).rhs
            # simplify what is inside the double-negation.
            expr = expr.simplification(assumptions, automation, innerExpr, inPlace).rhs
            return Equals(self, expr).prove(assumptions)
        # otherwise, just use the default simplification
        return Operation.simplification(self, assumptions, automation, innerExpr, inPlace)
                
    """
    def _closureTheorem(self, numberSet):
        import _theorems_
        if numberSet == Complexes:
            return _theorems_.negComplexClosure
        elif numberSet == Reals:
            return _theorems_.negRealClosure
        elif numberSet == Integers:
            return _theorems_.negIntClosure

    def _negativeTheorem(self):
        import _theorems_
        return _theorems_.negatedPositiveIsNegative

    def _positiveTheorem(self):
        import _theorems_
        return _theorems_.negatedNegativeIsPositive

    def _notEqZeroTheorem(self):
        import _theorems_
        return _theorems_.negNotEqZero
    """
    
    def asInt(self):
        '''
        Convert a literal integer into a Python int.  This
        only works if the operand is a literal int.
        '''
        return -self.operand.asInt()    
    """
    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, double negation or negating zero,
        derive and return this Neg expression equated with the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from ._theorems_ import negNeg, negZero
        from proveit.number import zero
        from proveit.logic import Equals
        if isinstance(self.operand, Neg):
            deduceInComplexes(self.operand.operand, assumptions)
            return negNeg.specialize({a:self.operand.operand}).checked(assumptions)
        elif self.operand == zero:
            return negZero
        return Equals(self, self)
        raise ValueError('Only trivial simplification is implemented (double negation or negating zero)')
        
    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, double negation or negating zero,
        derive and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
    """
    def string(self, **kwargs):
        return maybeFencedString('-'+self.operand.string(fence=True), **kwargs)

    def latex(self, **kwargs):
        return maybeFencedLatex('-'+self.operand.latex(fence=True), **kwargs)

    def distribution(self, assumptions=USE_DEFAULTS):
        '''
        Distribute negation through a sum, deducing and returning
        the equality between the original and distributed forms.
        '''
        from .theorems import distributeNegThroughSum, distributeNegThroughSubtract
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

    def factorization(self, theFactor, pull="left", groupFactor=None, groupRemainder=None, assumptions=USE_DEFAULTS):
        '''
        Pull out a factor from a negated expression, pulling it either to the "left" or "right".
        groupFactor and groupRemainder are not relevant but kept for compatibility with 
        other factor methods.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        FACTORING FROM NEGATION FROM A SUM NOT IMPLEMENTED YET.
        '''
        from ._theorems_ import negTimesPos, posTimesNeg, multNegOneLeft, multNegOneRight
        if isinstance(theFactor, Neg):
            if pull == 'left':
                thm = negTimesPos
            else:
                thm = posTimesNeg
            theFactor = theFactor.operand
        else:
            if pull == 'left':
                thm = posTimesNeg
            else:
                thm = negTimesPos
        if hasattr(self.operand, 'factor'):
            operandFactorEqn = self.operand.factor(theFactor, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
            eqn1 = operandFactorEqn.substitution(self.innerExpr().operand) 
            new_operand = operandFactorEqn.rhs
            eqn2 = thm.specialize({x:new_operand.operands[0], y:new_operand.operands[1]}, assumptions=assumptions).deriveReversed(assumptions)
            return eqn1.applyTransitivity(eqn2)
        else:
            if self.operand != theFactor:
                raise ValueError("%s is a factor in %s!"%(theFactor, self))     
            if thm==negTimesPos: thm=multNegOneLeft
            if thm==posTimesNeg: thm=multNegOneRight
            return thm.specialize({x:self.operand}, assumptions=assumptions).deriveReversed(assumptions)
