from proveit import Literal, Operation, maybeFencedString, maybeFencedLatex, InnerExpr, USE_DEFAULTS, ProofFailure
from proveit.logic import isIrreducibleValue
from proveit.number.sets import Integers, Reals, Complexes
from proveit._common_ import a, b, m, n, x, y, xx, AA, B, CC

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
    
    def doReducedSimplification(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Derive and return this negation expression equated with a simpler form.
        Deals with double negation specifically.
        '''
        from proveit.relation import TransRelUpdater

        expr = self
        # For convenience updating our equation:
        eq = TransRelUpdater(expr, assumptions)        
        # Handle double negation:
        if isinstance(self.operand, Neg):            
            # simplify double negation
            expr = eq.update(self.doubleNegSimplification(assumptions))
            # simplify what is inside the double-negation.
            expr = eq.update(expr.simplification(assumptions))
        return eq.relation
    
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Only handles -0 = 0 or double negation.
        '''
        from proveit.logic import EvaluationError
        from ._theorems_ import negatedZero
        from proveit.number import zero
        if self.operand == zero:
            return negatedZero
        if isinstance(self.operand, Neg) and isIrreducibleValue(self.operand.operand):
            return self.doubleNegSimplification(assumptions)
        raise EvaluationError(self, assumptions)
        
    def doubleNegSimplification(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import doubleNegation
        assert isinstance(self.operand, Neg), "Expecting a double negation: %s"%str(self)
        return doubleNegation.specialize({x:self.operand.operand}, 
                                         assumptions=assumptions)
    

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
    
    def string(self, **kwargs):
        return maybeFencedString('-'+self.operand.string(fence=True), **kwargs)

    def latex(self, **kwargs):
        return maybeFencedLatex('-'+self.operand.latex(fence=True), **kwargs)

    def distribution(self, assumptions=USE_DEFAULTS):
        '''
        Distribute negation through a sum, deducing and returning
        the equality between the original and distributed forms.
        '''
        from ._theorems_ import distributeNegThroughBinarySum
        from ._theorems_ import distributeNegThroughSubtract, distributeNegThroughSum
        from proveit.number import Add, num
        from proveit.relation import TransRelUpdater
        expr = self
        eq = TransRelUpdater(expr, assumptions) # for convenience updating our equation

        if isinstance(self.operand, Add):
            # Distribute negation through a sum.
            add_expr = self.operand
            if len(add_expr.operands)==2:
                # special case of 2 operands
                if isinstance(add_expr.operands[1], Neg):
                    expr = eq.update(distributeNegThroughSubtract.specialize({a:add_expr.operands[0], b:add_expr.operands[1].operand}, assumptions=assumptions))
                else:
                    expr = eq.update(distributeNegThroughBinarySum.specialize({a:add_expr.operands[0], b:add_expr.operands[1]}, assumptions=assumptions))
            else:
                # distribute the negation over the sum
                expr = eq.update(distributeNegThroughSum.specialize({n:num(len(add_expr.operands)), xx:add_expr.operands}), assumptions=assumptions)
            assert isinstance(expr, Add), "distributeNeg theorems are expected to yield an Add expression"
            # check for double negation
            for k, operand in enumerate(expr.operands):
                assert isinstance(operand, Neg), "Each term from distributeNegThroughSum is expected to be negated"
                if isinstance(operand.operand, Neg):
                    expr = eq.update(expr.innerExpr().operands[k].doubleNegSimplification())
            return eq.relation
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

    def innerNegMultSimplification(self, idx, assumptions=USE_DEFAULTS):
        '''
        Equivalence method to derive a simplification when negating
        a multiplication with a negated factor.  For example,
        -(a*b*(-c)*d) = a*b*c*d.
        See Mult.negSimplification where this may be used indirectly.
        '''
        from proveit.number import Mult, num
        from ._theorems_ import multNegLeftDouble, multNegRightDouble, multNegAnyDouble

        mult_expr = self.operand
        if not isinstance(mult_expr, Mult):
            raise ValueError("Operand expected to be a Mult expression for %s"%(idx, str(self)))
        if not isinstance(mult_expr.operands[idx], Neg):
            raise ValueError("Operand at the index %d expected to be a negation for %s"%(idx, str(mult_expr)))

        if len(mult_expr.operands)==2:
            if idx==0:
                return multNegLeftDouble.specialize({a:mult_expr.operands[1]}, assumptions=assumptions)
            else:
                return multNegRightDouble.specialize({a:mult_expr.operands[0]}, assumptions=assumptions)
        aVal = mult_expr.operands[:idx]
        bVal = mult_expr.operands[idx]
        cVal = mult_expr.operands[idx+1:]
        mVal = num(len(aVal))
        nVal = num(len(cVal))
        return multNegAnyDouble.specialize({m:mVal, n:nVal, AA:aVal, B:bVal, CC:cVal}, assumptions=assumptions)

# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(Neg, 'doubleNegSimplification', 'doubleNegSimplified', 'doubleNegSimplify')
InnerExpr.register_equivalence_method(Neg, 'distribution', 'distributed', 'distribute')
InnerExpr.register_equivalence_method(Neg, 'factorization', 'factorized', 'factor')
InnerExpr.register_equivalence_method(Neg, 'innerNegMultSimplification', 'innerNegMultSimplified', 'innerNegMultSimplify')
