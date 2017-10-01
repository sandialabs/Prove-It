from proveit import Literal, Operation, BinaryOperation, maybeFencedLatex, safeDummyVar
from proveit.logic import Equals
from proveit._common_ import w, x, y, z, wEtc, xEtc, zEtc

class Frac(BinaryOperation):
    # operator of the Fraction operation.
    _operator_ = Literal(stringFormat='frac', context=__file__)    
    
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands in fraction form.
        '''
        BinaryOperation.__init__(self, Frac._operator_, operandA, operandB)
        self.numerator = operandA
        self.denominator = operandB
    
    def string(self, **kwargs):
        '''
        Format as "fraction(A, B)".
        '''
        return Operation.string(self, **kwargs)

    def _closureTheorem(self, numberSet):
        import complex._theorems_
        import real._theorems_
        from proveit.number import Reals, RealsPos, Complexes
        if numberSet == Reals:
            return real._theorems_.fractionClosure
        elif numberSet == RealsPos:
            return real._theorems_.fractionPosClosure            
        elif numberSet == Complexes:
            return complex._theorems_.fractionClosure

    def _notEqZeroTheorem(self):
        import complex._theorems_
        return complex._theorems_.fractionNotEqZero

    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero numerator or one denominator,
        derive and return this fraction expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from _theorems_ import fracZeroNumer, fracOneDenom
        from number import zero, one
        if self.numerator == zero:
            return fracZeroNumer.specialize({x:self.denominator})
        elif self.denominator == one:
            return fracOneDenom.specialize({x:self.numerator})
        raise ValueError('Only trivial simplification is implemented (zero or one factors)')

    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero numerator or one denominator,
        derive this fraction expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
    def latex(self, **kwargs):
        # only fence if forceFence=True (a fraction within an exponentiation is an example of when fencing should be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False        
        return maybeFencedLatex(r'\frac{'+self.numerator.latex()+'}{'+self.denominator.latex()+'}', **kwargs)
    
    def combineExponents(self, assumptions=frozenset()):
        from _theorems_ import fracIntExp, fracNatPosExp
        from proveit.number import Exp
        if isinstance(self.numerator, Exp) and isinstance(self.denominator, Exp):
            if self.numerator.exponent == self.denominator.exponent:
                exponent = self.numerator.exponent
                try:
                    return fracNatPosExp.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
                except:
                    return fracIntExp.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
        raise Exception('Unable to combine exponents of this fraction')
        
    def cancel(self,operand, pull="left", assumptions=frozenset()):
        from proveit.number import Mult
        if self.numerator == self.denominator == operand:
            # x/x = 1
            from _theorems_ import fracCancelComplete
            return fracCancelComplete.specialize({x:operand}).checked(assumptions)
        
        if not isinstance(self.numerator,Mult):
            from _theorems_ import fracCancelNumerLeft
            newEq0 = self.denominator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(self.numerator,safeDummyVar(self)),safeDummyVar(self)).checked(assumptions)
            newEq1 = fracCancelNumerLeft.specialize({x:operand,y:newEq0.rhs.denominator.operands[1]})
            return newEq0.applyTransitivity(newEq1)
            
        assert isinstance(self.numerator,Mult)
        if isinstance(self.denominator,Mult):
            from _theorems_ import fracCancelLeft
            newEq0 = self.numerator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(safeDummyVar(self),self.denominator),safeDummyVar(self)).checked(assumptions)
            newEq1 = self.denominator.factor(operand, pull = pull, groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(newEq0.rhs.numerator,safeDummyVar(self)),safeDummyVar(self)).checked(assumptions)
            newEq2 = fracCancelLeft.specialize({x:operand,y:newEq1.rhs.numerator.operands[1],z:newEq1.rhs.denominator.operands[1]})
            return newEq0.applyTransitivity(newEq1).applyTransitivity(newEq2)
#            newFracIntermediate = self.numerator.factor(operand).proven().rhsSubstitute(self)
#            newFrac = self.denominator.factor(operand).proven().rhsSubstitute(newFracIntermediate)
#            numRemainingOps = newFrac.numerator.operands[1:]
#            denomRemainingOps = newFrac.denominator.operands[1:]
#            return fracCancel1.specialize({x:operand,Etcetera(y):numRemainingOps,Etcetera(z):denomRemainingOps})
        else:
            from _theorems_ import fracCancelDenomLeft
            newEq0 = self.numerator.factor(operand,pull=pull,groupFactor = True, groupRemainder = True, assumptions=assumptions).substitution(Fraction(safeDummyVar(self),self.denominator),safeDummyVar(self)).checked(assumptions)
            newEq1 = fracCancelDenomLeft.specialize({x:operand,y:newEq0.rhs.numerator.operands[1]})
            return newEq0.applyTransitivity(newEq1)
#            newFrac = self.numerator.factor(operand).proven().rhsSubstitute(self)
#            numRemainingOps = newFrac.numerator.operands[1:]
#            return fracCancel2.specialize({x:operand,Etcetera(y):numRemainingOps})

    def distribute(self, assumptions=frozenset()):
        r'''
        Distribute the denominator through the numerate.  
        Returns the equality that equates self to this new version.
        Examples: 
            :math:`(a + b + c) / d = a / d + b / d + c / d`
            :math:`(a - b) / d = a / d - b / d`
            :math:`\left(\sum_x f(x)\right / y = \sum_x [f(x) / y]`
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.            
        '''
        from proveit.number import Add, Sub, Sum
        from _theorems_ import distributeFractionThroughSum, distributeFractionThroughSubtract, distributeFractionThroughSummation
        if isinstance(self.numerator, Add):
            return distributeFractionThroughSum.specialize({xEtc:self.numerator.operands, y:self.denominator})
        elif isinstance(self.numerator, Sub):
            return distributeFractionThroughSubtract.specialize({x:self.numerator.operands[0], y:self.numerator.operands[1], z:self.denominator})
        elif isinstance(self.numerator, Sum):
            # Should deduce in Complexes, but distributeThroughSummation doesn't have a domain restriction right now
            # because this is a little tricky.   To do.
            #deduceInComplexes(self.operands, assumptions)
            yEtcSub = self.numerator.indices
            Pop, Pop_sub = Operation(P, self.numerator.indices), self.numerator.summand
            S_sub = self.numerator.domain
            dummyVar = safeDummyVar(self)            
            spec1 = distributeFractionThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yEtc:yEtcSub, z:dummyVar})
            return spec1.deriveConclusion().specialize({dummyVar:self.denominator})
        else:
            raise Exception("Unsupported operand type to distribute over: " + self.numerator.__class__)

    def factor(self,theFactor,pull="left", groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a factor from a fraction, pulling it either to the "left" or "right".
        The factor may be a product or fraction itself.  
        If groupFactor is True and theFactor is a product, it will be grouped together as a 
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''        
        from _theorems_ import fracInProdRev, prodOfFracsRev, prodOfFracsLeftNumerOneRev, prodOfFracsRightNumerOneRev
        from proveit.number import Mult, num
        dummyVar = safeDummyVar(self)
        eqns = []
        if isinstance(theFactor, Frac):
            # factor the operand denominator out of self's denominator
            denomFactorEqn = self.denominator.factor(theFactor.denominator, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
            factoredDenom = denomFactorEqn.rhs
            eqns.append(denomFactorEqn.substitution(Frac(self.numerator, dummyVar), dummyVar))
            if theFactor.numerator != num(1) and self.numerator != num(1):
                # factor the operand numerator out of self's numerator
                numerFactorEqn = self.numerator.factor(theFactor.numerator, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
                factoredNumer = numerFactorEqn.rhs
                eqns.append(numerFactorEqn.substitution(Frac(dummyVar, factoredDenom), dummyVar))
                # factor the two fractions
                eqns.append(prodOfFracsRev.specialize({x:factoredNumer.operands[0], y:factoredNumer.operands[1], 
                                                    z:factoredDenom.operands[0], w:factoredDenom.operands[1]}))
            else:
                # special case: one of the numerators is equal to one, no numerator factoring to be done
                if (pull == 'left') == (theFactor.numerator == num(1)):
                    thm = prodOfFracsLeftNumerOneRev
                else:
                    thm = prodOfFracsRightNumerOneRev
                # factor the two fractions
                eqns.append(thm.specialize({x:self.numerator, y:factoredDenom.operands[0], z:factoredDenom.operands[1]}))
        else:
            numerFactorEqn = self.numerator.factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=assumptions)
            factoredNumer = numerFactorEqn.rhs
            eqns.append(numerFactorEqn.substitution(Frac(dummyVar, self.denominator), dummyVar))
            # factor the numerator factor from the fraction
            if pull == 'left':
                wEtcSub = factoredNumer.operands[:-1]
                xSub = factoredNumer.operands[-1]
                zEtcSub = []
            elif pull == 'right':
                wEtcSub = []
                xSub = factoredNumer.operands[0]
                zEtcSub = factoredNumer.operands[1:]
            eqns.append(fracInProdRev.specialize({wEtc:wEtcSub, x:xSub, y:self.denominator, zEtc:zEtcSub}))
            num = len(theFactor.operands) if isinstance(theFactor, Mult) else 1
            if groupFactor and num > 1:
                if pull=='left':
                    eqns.append(eqns[-1].rhs.group(endIdx=num, assumptions=assumptions))
                elif pull=='right':
                    eqns.append(eqns[-1].rhs.group(startIdx=-num, assumptions=assumptions))           
        return Equals(eqns[0].lhs, eqns[-1].rhs).prove(assumptions)

