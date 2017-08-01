from proveit import Literal, Operation, AssociativeOperation, Etcetera, MultiVariable
from proveit.logic import Equals
from proveit.number.sets import Reals, RealsPos, Complexes, zero, one
from proveit._common_ import a, b, c, n, x, vEtc, wEtc, xEtc, yEtc, zEtc, S

class Mult(AssociativeOperation):
    # operator of the Mult operation.
    _operator_ = Literal(stringFormat='*', latexFormat=r'\cdot', context=__file__)
    
    def __init__(self, *operands):
        r'''
        Multiply together any number of operands from first operand.
        '''
        AssociativeOperation.__init__(self, Mult._operator_, *operands)
        self.factors = operands
   
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.multRealClosure
        elif numberSet == RealsPos:
            return theorems.multRealPosClosure            
        elif numberSet == Complexes:
            return complex.theorems.multComplexClosure

    def _notEqZeroTheorem(self):
        import theorems
        return theorems.multNotEqZero
    
    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one factor,
        derive and return this multiplication expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from theorems import multOne, multZero
        eq = Equation()
        expr = self
        try:
            zeroIdx = self.operands.index(zero)
            # there is a zero in the product.  We can simplify that.
            if zeroIdx > 0:
                # commute it so that the zero comes first
                expr = eq.update(expr.commute(0, zeroIdx, zeroIdx, zeroIdx+1, assumptions)).rhs
            if len(expr.operands) > 2:
                # group the other operands so there are only two at the top level
                expr = eq.update(expr.group(1, len(expr.operands), assumptions)).rhs
            deduceInComplexes(expr.operands[1], assumptions)
            return eq.update(multZero.specialize({x:expr.operands[1]}))
        except ValueError:
            pass # no zero factor
        try:
            oneIdx = expr.operands.index(one)
            # there is a one in the product.  We can simplify that.
            if oneIdx > 0:
                # commute it so that the one comes first
                expr = eq.update(expr.commute(0, oneIdx, oneIdx, oneIdx+1, assumptions)).rhs                
            if len(expr.operands) > 2:
                # group the other operands so there are only two at the top level
                expr = eq.update(expr.group(1, len(expr.operands), assumptions)).rhs
            deduceInComplexes(expr.operands[1], assumptions)
            return eq.update(multOne.specialize({x:expr.operands[1]}))
        except ValueError:
            pass # no one factor
        raise ValueError('Only trivial simplification is implemented (zero or one factors)')

    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one factor,
        derive this multiplication expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
    def commute(self, startIdx1=None, endIdx1=None, startIdx2=None, endIdx2=None, assumptions=frozenset()):
        '''
        Commute self.operands[startIdx1:endIdx1] with self.operands[startIdx2:endIdx2].  
        The default, if no indices are provided, is to commute the first operand with the rest
        (convenient especially when there are just two operands).
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from theorems import multComm
        if startIdx1 is None and endIdx1 is None and startIdx2 is None and endIdx2 is None:
            stattIdx1, endIdx1, startIdx2, endIdx2 = 0, 1, 1, None
        nOperands = len(self.operands)
        start1, stop1, _ = slice(startIdx1, endIdx1).indices(nOperands)
        start2, stop2, _ = slice(startIdx2, endIdx2).indices(nOperands)
        if start1  > start2:
            # swap 1 and 2 so that 1 comes first
            startIdx1, endIdx1, startIdx2, endIdx2 = startIdx2, endIdx2, startIdx1, endIdx2
            start1, stop1, start2, stop2 = start2, stop2, start1, stop1
        if stop1 > start2:
            raise ValueError("Cannot commute verlapping sets of operands")
        vSub = self.operands[:startIdx1] if startIdx1 is not None else []
        wSub = self.operands[startIdx1:endIdx1]
        xSub = self.operands[endIdx1:startIdx2]
        ySub = self.operands[startIdx2:endIdx2]
        zSub = self.operands[endIdx2:] if endIdx2 is not None else []
        deduceInComplexes(self.operands, assumptions)
        return multComm.specialize({vEtc:vSub, wEtc:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}, assumptions=assumptions)

    def group(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Group together (associate as a sub-product wrapped in parenthesis)
        consecutive operands, self.operands[startIdx:endIdx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from axioms import multAssoc
        deduceInComplexes(self.operands, assumptions)
        xSub = self.operands[:startIdx] if startIdx is not None else []
        ySub = self.operands[startIdx:endIdx]
        zSub = self.operands[endIdx:] if endIdx is not None else []
        return multAssoc.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def ungroup(self, idx, assumptions=frozenset()):
        '''
        Ungroup (un-associate a sub-product wrapped in parenthesis)
        an operand, self.operands[idx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        if not isinstance(self.operands[idx], Mult):  
            raise ValueError("Selected term is not a Mult expression")

        from theorems import multAssocRev
        deduceInComplexes(self.operands, assumptions)
        deduceInComplexes(self.operands[idx].operands, assumptions)
        xSub = self.operands[:idx] if idx is not None else []
        ySub = self.operands[idx].operands
        zSub = self.operands[idx+1:] if idx is not None else []
        return multAssocRev.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)
    
    def index(self, theFactor, alsoReturnNum=False):
        '''
        Return the starting index of theFactor, which may be a single operand,
        a list of consecutive operands, or a Mult expression that represents
        the product of the list of consecutive operands.  If alsoReturnNum is
        True, return a tuple of the index and number of operands for theFactor.
        '''
        if isinstance(theFactor, Mult):
            theFactor = theFactor.operands
        if hasattr(theFactor, '__getitem__') and hasattr(theFactor, '__len__'):
            # multiple operands in theFactor
            firstFactor = theFactor[0]
            num = len(theFactor)
            idx = -1
            try:
                while True:
                    idx = self.operands.index(firstFactor, idx+1)
                    if tuple(self.operands[idx:idx+num]) == tuple(theFactor):
                        break # found it all!
            except ValueError:
                raise ValueError("Factor is absent!")
        else:
            num = 1
            try:
                idx = self.operands.index(theFactor)
            except ValueError:
                raise ValueError("Factor is absent!")        
        return (idx, num) if alsoReturnNum else idx
    
    def pull(self, startIdx=None, endIdx=None, direction='left', assumptions=frozenset()):
        '''
        Pull a subset of consecutive operands, self.operands[startIdx:endIdx],
        to one side or another. Returns the equality that equates self to 
        this new version.  Give any assumptions necessary to prove that the 
        operands are in Complexes so that the commutation theorem is applicable.
        '''
        from proveit.logic.equality.axioms import equalsReflexivity
        if direction == "left": # pull the factor(s) to the left
            if startIdx == 0 or startIdx is None:
                return equalsReflexivity.specialize({x:self}).checked() # no move necessary
            return self.commute(None, startIdx, startIdx, endIdx, assumptions=assumptions)
        elif direction == "right": # pull the factor(s) to the right
            if endIdx == len(self.operands) or endIdx is None:
                return equalsReflexivity.specialize({x:self}).checked() # no move necessary
            return self.commute(startIdx, endIdx, endIdx, None, assumptions=assumptions)
        else:
            raise ValueError("Invalid pull direction!  (Acceptable values are \"left\" and \"right\".)")

    def distribute(self, index=None, assumptions=frozenset()):
        r'''
        Distribute through the operand at the given index.  
        Returns the equality that equates self to this new version.
        Examples: 
            :math:`a (b + c + a) d = a b d + a c d + a a d`
            :math:`a (b - c) d = a b d - a c d`
            :math:`a \left(\sum_x f(x)\right c = \sum_x a f(x) c`
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.            
        '''
        from theorems import distributeThroughSum, distributeThroughSubtract, distributeThroughSummation
        from proveit.number.division.theorems import fracInProd, prodOfFracs
        from proveit.number import Fraction, Add, Sub, Sum
        if index is None and len(self.factors) == 2 and all(isinstance(factor, Fraction) for factor in self.factors):
            deduceInComplexes(self.factors[0].operands, assumptions)
            deduceInComplexes(self.factors[1].operands, assumptions)
            return prodOfFracs.specialize({x:self.factors[0].numerator, y:self.factors[1].numerator, z:self.factors[0].denominator, w:self.factors[1].denominator})
        operand = self.operands[index]
        if isinstance(operand, Add):
            deduceInComplexes(self.operands[:index], assumptions)
            deduceInComplexes(self.operands[index].operands, assumptions)
            deduceInComplexes(self.operands[index+1:], assumptions)
            return distributeThroughSum.specialize({xEtc:self.operands[:index], yEtc:self.operands[index].operands, zEtc:self.operands[index+1:]})
        elif isinstance(operand, Sub):
            deduceInComplexes(self.operands[:index], assumptions)
            deduceInComplexes(self.operands[index].operands, assumptions)
            deduceInComplexes(self.operands[index+1:], assumptions)
            return distributeThroughSubtract.specialize({wEtc:self.operands[:index], x:self.operands[index].operands[0], y:self.operands[index].operands[1], zEtc:self.operands[index+1:]})
        elif isinstance(operand, Fraction):            
            deduceInComplexes(self.operands[:index], assumptions)
            deduceInComplexes(self.operands[index].operands, assumptions)
            deduceInComplexes(self.operands[index+1:], assumptions)
            eqn = fracInProd.specialize({wEtc:self.operands[:index], x:self.operands[index].operands[0], y:self.operands[index].operands[1], zEtc:self.operands[index+1:]})            
            try:
                # see if the numerator can simplify (e.g., with a one factor)
                numerSimplification = eqn.rhs.numerator.simplification(assumptions=assumptions)
                dummyVar = eqn.safeDummyVar()
                return numerSimplification.rhsSubstitute(Equals(eqn.lhs, Fraction(dummyVar, eqn.rhs.denominator)), dummyVar)
            except:
                return eqn
        elif isinstance(operand, Sum):
            deduceInComplexes(self.operands, assumptions)
            yEtcSub = operand.indices
            Pop, Pop_sub = Operation(P, operand.indices), operand.summand
            S_sub = operand.domain
            xDummy, zDummy = self.safeDummyVars(2)
            spec1 = distributeThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yEtc:yEtcSub, 
                                                           xEtc:Etcetera(MultiVariable(xDummy)), zEtc:Etcetera(MultiVariable(zDummy))}).checked()
            return spec1.deriveConclusion().specialize({Etcetera(MultiVariable(xDummy)):self.operands[:index], \
                                                        Etcetera(MultiVariable(zDummy)):self.operands[index+1:]})
        else:
            raise Exception("Unsupported operand type to distribute over: " + str(operand.__class__))
        
    def factor(self,theFactor,pull="left", groupFactor=True, groupRemainder=False, assumptions=frozenset()):
        '''
        Factor out "theFactor" from this product, pulling it either to the "left" or "right".
        If "theFactor" is a product, this may factor out a subset of the operands as
        long as they are next to each other (use commute to make this happen).  If
        there are multiple occurrences, the first occurrence is used.  If groupFactor is
        True and theFactor is a product, these operands are grouped together as a sub-product.
        If groupRemainder is True and there are multiple remaining operands (those not in
        "theFactor"), then these remaining operands are grouped together as a sub-product.
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        idx, num = self.index(theFactor, alsoReturnNum = True)
        eq = Equation(self.pull(idx, idx+num, pull, assumptions))
        if groupFactor and num > 1:
            if pull == 'left':  # use 0:num type of convention like standard pythong
                eq.update(eq.eqExpr.rhs.group(endIdx=num, assumptions=assumptions))
            elif pull == 'right':
                eq.update(eq.eqExpr.rhs.group(startIdx=-num, assumptions=assumptions))
        if groupRemainder and len(self.operands)-num > 1:
            # if the factor has been group, effectively there is just 1 factor operand now
            numFactorOperands = 1 if groupFactor else num
            if pull == 'left':           
                eq.update(eq.eqExpr.rhs.group(startIdx=numFactorOperands, assumptions=assumptions))
            elif pull == 'right':
                eq.update(eq.eqExpr.rhs.group(endIdx=-numFactorOperands, assumptions=assumptions))
        return eq.eqExpr.checked(assumptions)
        
    def combineExponents(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Equates $a^b a^c$ to $a^{b+c}$, $a^b a^{-c}$ to $a^{b-c}$,  $a^b a$ to $a^{b+1}, $a a^b$ to $a^{1+b},
        or equates $a^c b^c$ to $(a b)^c$.
        '''
        from proveit.number.exponentiation.theorems import expOfPositivesProdRev, intExpOfProdRev, natsPosExpOfProdRev
        from proveit.number.exponentiation.theorems import sumInExpRev, diffInExpRev, diffFracInExpRev
        from proveit.number.exponentiation.theorems import addOneRightInExpRev, addOneLeftInExpRev
        from proveit.number.exponentiation.theorems import prodOfSqrts
        from proveit.number import Sqrt, Exp, Neg, Fraction
        if startIdx is not None or endIdx is not None:
            dummyVar = self.safeDummyVar()
            grouped = self.group(startIdx, endIdx, assumptions=assumptions)
            innerCombineExponents = grouped.rhs.factors[startIdx].combineExponents(assumptions=assumptions)
            combineInGroup = innerCombineExponents.substitution(Mult(*(self.factors[:startIdx] + (dummyVar,) + self.factors[endIdx:])), dummyVar)
            return grouped.applyTransitivity(combineInGroup)
        if all(isinstance(factor, Sqrt) for factor in self.factors):
            # combine the square roots into one square root
            factorBases = [factor.base for factor in self.factors]
            deduceInRealsPos(factorBases, assumptions)
            return prodOfSqrts.specialize({xEtc:factorBases})
        if len(self.operands) != 2 or not isinstance(self.operands[0], Exp) or not isinstance(self.operands[1], Exp):
            if len(self.operands) == 2 and isinstance(self.operands[0], Exp) and self.operands[0].base == self.operands[1]:
                # Of the form a^b a
                deduceInComplexes(self.operands[1], assumptions)
                deduceNotZero(self.operands[1], assumptions)
                deduceInComplexes(self.operands[0].exponent, assumptions)
                return addOneRightInExpRev.specialize({a:self.operands[1], b:self.operands[0].exponent})
            elif len(self.operands) == 2 and isinstance(self.operands[1], Exp) and self.operands[1].base == self.operands[0]:
                # Of the form a a^b
                deduceInComplexes(self.operands[0], assumptions)
                deduceNotZero(self.operands[0], assumptions)
                deduceInComplexes(self.operands[1].exponent, assumptions)
                return addOneLeftInExpRev.specialize({a:self.operands[0], b:self.operands[1].exponent})
            raise Exception('Combine exponents only implemented for a product of two exponentiated operands (or a simple variant)')
        if self.operands[0].base == self.operands[1].base:
            # Same base: a^b a^c = a^{b+c}$, or something similar
            aSub = self.operands[0].base
            deduceNotZero(aSub, assumptions)
            bSub = self.operands[0].exponent
            if isinstance(self.operands[1].exponent, Neg):
                # equate $a^b a^{-c} = a^{b-c}$
                thm = diffInExpRev
                cSub = self.operands[1].exponent.operand
            elif isinstance(self.operands[1].exponent, Fraction) and isinstance(self.operands[1].exponent.numerator, Neg):
                # equate $a^b a^{-c/d} = a^{b-c/d}$
                thm = diffFracInExpRev
                cSub = self.operands[1].exponent.numerator.operand
                dSub = self.operands[1].exponent.denominator
                deduceInComplexes([aSub, bSub, cSub, dSub], assumptions=assumptions)
                return thm.specialize({a:aSub, b:bSub, c:cSub, d:dSub})
            else:
                # standard $a^b a^c = a^{b+c}$
                thm = sumInExpRev
                cSub = self.operands[1].exponent
        elif self.operands[0].exponent == self.operands[1].exponent:
            # Same exponent: equate $a^c b^c = (a b)^c$
            aSub = self.operands[0].base
            bSub = self.operands[1].base
            expSub = self.operands[0].exponent
            try:
                deduceInNaturalsPos(expSub, assumptions)
                deduceInComplexes([aSub, bSub], assumptions)
                return natsPosExpOfProdRev.specialize({n:expSub}).specialize({a:aSub, b:bSub})
            except:
                pass
            try:
                deduceInIntegers(expSub, assumptions)
                deduceInComplexes([aSub, bSub], assumptions)
                deduceNotZero([aSub, bSub], assumptions)
                return intExpOfProdRev.specialize({n:expSub}).specialize({a:aSub, b:bSub})
            except:
                deduceInRealsPos([aSub, bSub], assumptions)
                deduceInComplexes([expSub], assumptions)
                return expOfPositivesProdRev.specialize({c:expSub}).specialize({a:aSub, b:bSub})
        else:
            raise Exception('Product is not in the correct form to combine exponents: ' + str(self))
        deduceInComplexes([aSub, bSub, cSub], assumptions=assumptions)
        return thm.specialize({a:aSub, b:bSub, c:cSub})
