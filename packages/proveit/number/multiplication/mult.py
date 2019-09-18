from proveit import Literal, Operation, USE_DEFAULTS, ProofFailure, InnerExprMethodsObject
from proveit.logic import Equals, InSet
from proveit.number.sets import Integers, Naturals, NaturalsPos, Reals, RealsPos, Complexes
import proveit.number.numeral.deci
from proveit.number.numeral.deci import DIGITS
from proveit._common_ import a, b, c, d, l, m, n, v, w, x, y, z, vv, ww, xx, yy, zz, S, A, B, C, D, E, AA, BB, CC, DD, EE
from proveit.abstract_algebra.inner_expr_mixins import CommutativeAndAssociativeInnerExprMixin, DistributiveInnerExprMixin
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, groupCommutation, pairwiseEvaluation
from proveit import TransRelUpdater


class Mult(Operation):
    # operator of the Mult operation.
    _operator_ = Literal(stringFormat='*', latexFormat=r'\cdot', context=__file__)
    
    # Multiplying two numerals may import a theorem for the evaluation.
    # Track which ones we have encountered already.
    multipliedNumerals = set()
        
    def __init__(self, *operands):
        r'''
        Multiply together any number of operands from first operand.
        '''
        Operation.__init__(self, Mult._operator_, operands)
        self.factors = operands
        if len(self.factors)==2 and all(factor in DIGITS for factor in self.factors):
            if self not in Mult.multipliedNumerals:
                try:
                    # for single digit addition, import the theorem that provides the evaluation
                    Mult.multipliedNumerals.add(self)
                    proveit.number.numeral.deci._theorems_.__getattr__('mult_%d_%d'%(self.factors[0].asInt(), self.factors[1].asInt()))
                except:
                    # may fail before the relevent _commons_ and _theorems_ have been generated
                    pass # and that's okay
    
    def innerExprMethodsObject(self, innerExpr):
        return InnerMultiplication(innerExpr)
        
    def deduceInNumberSet(self, numberSet, assumptions=USE_DEFAULTS):
        # edited by JML 7/20/19
        from ._theorems_ import multIntClosure, multIntClosureBin, multNatClosure, multNatClosureBin, multNatPosClosure, multNatClosureBin, multRealClosure, multRealClosureBin, multRealPosClosure, multRealPosClosureBin, multComplexClosure, multComplexClosureBin
        from proveit.number import num
        if hasattr(self, 'number_set'):
            numberSet = numberSet.number_set
        bin = False
        if numberSet == Integers:
            if len(self.operands) == 2:
                thm = multIntClosureBin
                bin = True
            else:
                thm = multIntClosure
        elif numberSet == Naturals:
            if len(self.operands) == 2:
                thm = multNatsClosureBin
                bin = True
            else:
                thm = multNatsClosure
        elif numberSet == NaturalsPos:
            if len(self.operands) == 2:
                thm = multNatsPosClosureBin
                bin = True
            else:
                thm = multNatsPosClosure
        elif numberSet == Reals:
            if len(self.operands) == 2:
                thm = multRealClosureBin
                bin = True
            else:
                thm = multRealClosure
        elif numberSet == RealsPos:
            if len(self.operands) == 2:
                thm = multRealsPosClosureBin
                bin = True
            else:
                thm = multRealPosClosure
        elif numberSet == Complexes:
            if len(self.operands) == 2:
                thm = multComplexClosureBin
                bin = True
            else:
                thm = multComplexClosure
        else:
            raise ProofFailure(InSet(self, numberSet), assumptions, "'deduceInNumberSet' not implemented for the %s set"%str(numberSet))
        from proveit._common_ import AA
        # print("thm", thm)
        # print("self in deduce in number set", self)
        # print("self.operands", self.operands)
        if bin:
            return thm.specialize({a:self.operands[0], b:self.operands[1]}, assumptions=assumptions)
        return thm.specialize({m:num(len(self.operands)),AA:self.operands}, assumptions=assumptions)
    
    def notEqual(self, rhs, assumptions=USE_DEFAULTS):
        from ._theorems_ import multNotEqZero
        if rhs == zero:
            return multNotEqZero.specialize({xMulti:self.operands}, assumptions=assumptions)
        raise ProofFailure(Equals(self, zero), assumptions, "'notEqual' only implemented for a right side of zero")
    
    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        Derive and return this multiplication expression equated with a simpler form.
        Deals with factors of one and disassociating any nested multiplications
        (doReducedEvaluation deals with factors of 0).
        '''
        from ._theorems_ import multOneLeft, multOneRight, multOneAny
        from proveit.logic import Equals
        from proveit.number import one
        
        expr = self
        eq = TransRelUpdater(self, assumptions) # for convenience updating our equation
        
        # ungroup the expression (disassociate nested multiplications).
        n = 0
        length = len(expr.operands) - 1
        while n < length:
            # loop through all operands
            # print("n, length", n, length)
            if isinstance(expr.operands[n], Mult):
                # if it is grouped, ungroup it
                # print("to ungroup")
                expr = eq.update(expr.disassociation(n, assumptions))
                # print("new expr", expr)
            else:
                n += 1
            length = len(expr.operands)
        
        shift = 0
        one_locations = [i for i, operand in enumerate(self.operands) if operand==one]
        for idx in one_locations:
            idx -= shift
            if len(expr.operands)==2:
                if idx==0:
                    return multOneLeft.specialize({x:expr.operands[1]}, assumptions=assumptions)
                else:
                    return multOneRight.specialize({x:expr.operands[0]}, assumptions=assumptions)
            Afactors = expr.operands[:idx]
            Bfactors = expr.operands[idx+1:]
            simp = multOneAny.specialize({m:len(Afactors), n:len(Bfactors), AA:Afactors, BB:Bfactors}, assumptions=assumptions)
            expr = eq.update(simp)
            shift += 1

        return eq.relation

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        Derive and return this multiplication expression equated with an irreducible value.
        Handle the trivial case of a zero factor or use the default evaluation.
        '''
        from ._theorems_ import multZeroLeft, multZeroRight, multZeroAny
        from proveit.logic import SimplificationError
        from proveit.number import zero
        try:
            zeroIdx = self.operands.index(zero)
            if len(self.operands)==2:
                if zeroIdx==0:
                    return multZeroLeft.specialize({x:self.operands[1]}, assumptions=assumptions)
                else:
                    return multZeroRight.specialize({x:self.operands[0]}, assumptions=assumptions)
            Afactors = self.operands[:zeroIdx]
            Bfactors = self.operands[zeroIdx+1:]
            return multZeroAny.specialize({m:len(Afactors), n:len(Bfactors), AA:Afactors, BB:Bfactors}, assumptions=assumptions)
        except (ValueError, ProofFailure):
            # use the default if zero is not one of the factors:
            raise SimplificationError("Currently only evaluating multiplication with a 0 operand.  Straightfored to implement a better way when someone can get around to it -- see the Add doReducedEvaluation method.")
        
        if len(self.operands) > 2:
            return pairwiseEvaluation(self, assumptions)

        raise SimplificationError("Unable to evaluate %s"%str(self))
        
    
    def conversionToAddition(self, assumptions=USE_DEFAULTS):
        '''
        From multiplication by an integer as the first factor,
        derive and return the equivalence of this multiplication
        to a repeated addition; for example, 3*c = c + c + c.
        '''
        from ._axioms_ import multDef
        from proveit.number import num
        if hasattr(self.operands[0], 'asInt'):
            reps = self.operands[0].asInt()
        else:
            raise ValueError("Cannot 'expandAsAddition' unless the first operand is a literal integer: %s"%str(self))

        expr = self
        eq = TransRelUpdater(self, assumptions) # for convenience updating our equation
        # Group together the remaining factors if necessary:
        if len(self.operands) > 2:
            expr = eq.update(expr.association(1, len(self.operands)-1, assumptions))
        xVal = self.operands[1]          
        eq.update(multDef.specialize({m:num(reps), AA:[xVal]*reps, x:xVal}, assumptions=assumptions))
        return eq.relation
    
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
                    idx = self.operands.index(firstFactor, start=idx+1)
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
    
    def pull(self, startIdx=None, endIdx=None, direction='left', assumptions=USE_DEFAULTS):
        '''
        Pull a subset of consecutive operands, self.operands[startIdx:endIdx],
        to one side or another. Returns the equality that equates self to 
        this new version.  Give any assumptions necessary to prove that the 
        operands are in Complexes so that the commutation theorem is applicable.
        '''
        if direction == "left": # pull the factor(s) to the left
            if startIdx == 0 or startIdx is None:
                return Equals(self, self).prove(assumptions) # no move necessary
            return self.groupCommutation(None, startIdx, startIdx, endIdx, assumptions=assumptions)
        elif direction == "right": # pull the factor(s) to the right
            if endIdx == len(self.operands) or endIdx is None:
                return Equals(self, self).prove(assumptions) # no move necessary
            return self.groupCommutation(startIdx, endIdx, endIdx, None, assumptions=assumptions)
        else:
            raise ValueError("Invalid pull direction!  (Acceptable values are \"left\" and \"right\".)")

    def distribution(self, idx=None, assumptions=USE_DEFAULTS):
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
        from ._theorems_ import distributeThroughSum, distributeThroughSubtract, distributeThroughSummation
        from proveit.number.division._theorems_ import fracInProd, prodOfFracs
        from proveit.number import frac, Div, Add, subtract, Sum
        if idx is None and len(self.factors) == 2 and all(isinstance(factor, Div) for factor in self.factors):
            return prodOfFracs.specialize({x:self.factors[0].numerator, y:self.factors[1].numerator, z:self.factors[0].denominator, w:self.factors[1].denominator}, assumptions=assumptions)
        operand = self.operands[idx]
        if isinstance(operand, Add):
            return distributeThroughSum.specialize({xMulti:self.operands[:idx], yMulti:self.operands[idx].operands, zMulti:self.operands[idx+1:]}, assumptions=assumptions)
        elif isinstance(operand, subtract):
            return distributeThroughSubtract.specialize({wMulti:self.operands[:idx], x:self.operands[idx].operands[0], y:self.operands[idx].operands[1], zMulti:self.operands[idx+1:]}, assumptions=assumptions)
        elif isinstance(operand, Div):            
            eqn = fracInProd.specialize({wMulti:self.operands[:idx], x:self.operands[idx].operands[0], y:self.operands[idx].operands[1], zMulti:self.operands[idx+1:]}, assumptions=assumptions)            
            try:
                # see if the numerator can simplify (e.g., with a one factor)
                numerSimplification = eqn.rhs.numerator.simplification(assumptions=assumptions)
                dummyVar = eqn.safeDummyVar()
                return numerSimplification.subRightSideInto(Equals(eqn.lhs, frac(dummyVar, eqn.rhs.denominator)), dummyVar)
            except:
                return eqn
        elif isinstance(operand, Sum):
            yMultiSub = operand.indices
            Pop, Pop_sub = Operation(P, operand.indices), operand.summand
            S_sub = operand.domain
            xDummy, zDummy = self.safeDummyVars(2)
            spec1 = distributeThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yMulti:yMultiSub, 
                                                           xMulti:Etcetera(MultiVariable(xDummy)), zMulti:Etcetera(MultiVariable(zDummy))}, assumptions=assumptions)
            return spec1.deriveConclusion().specialize({Etcetera(MultiVariable(xDummy)):self.operands[:idx], \
                                                        Etcetera(MultiVariable(zDummy)):self.operands[idx+1:]}, assumptions=assumptions)
        else:
            raise Exception("Unsupported operand type to distribute over: " + str(operand.__class__))
        
    def factorization(self,theFactor,pull="left", groupFactor=True, groupRemainder=False, assumptions=USE_DEFAULTS):
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
        idx, num = self.index(theFactor, alsoReturnNum=True)
        expr = self.groupCommutation(idx, 0 if pull=='left' else -1, length=num, assumptions=assumptions)
        if groupFactor and num > 1:
            if pull == 'left':  # use 0:num type of convention like standard pythong
                expr = expr.rhs.group(endIdx=num, assumptions=assumptions)
            elif pull == 'right':
                expr = expr.rhs.group(startIdx=-num, assumptions=assumptions)
        if groupRemainder and len(self.operands)-num > 1:
            # if the factor has been group, effectively there is just 1 factor operand now
            numFactorOperands = 1 if groupFactor else num
            if pull == 'left':           
                expr = expr.rhs.group(startIdx=numFactorOperands, assumptions=assumptions)
            elif pull == 'right':
                expr = expr.rhs.group(endIdx=-numFactorOperands, assumptions=assumptions)
        return Equals(self, expr.rhs)
        
    def combineExponents(self, startIdx=None, endIdx=None, assumptions=USE_DEFAULTS):
        '''
        Equates $a^b a^c$ to $a^{b+c}$, $a^b a^{-c}$ to $a^{b-c}$,  $a^b a$ to $a^{b+1}, $a a^b$ to $a^{1+b},
        or equates $a^c b^c$ to $(a b)^c$.
        '''
        from proveit.number.exponentiation._theorems_ import expOfPositivesProd, intExpOfProd, natsPosExpOfProd
        from proveit.number.exponentiation._theorems_ import sumInExp, diffInExp, diffFracInExp
        from proveit.number.exponentiation._theorems_ import addOneRightInExp, addOneLeftInExp
        from proveit.number.exponentiation._theorems_ import prodOfSqrts
        from proveit.number import Sqrt, Exp, Neg, Div
        if startIdx is not None or endIdx is not None:
            dummyVar = self.safeDummyVar()
            grouped = self.group(startIdx, endIdx, assumptions=assumptions)
            innerCombineExponents = grouped.rhs.factors[startIdx].combineExponents(assumptions=assumptions)
            combineInGroup = innerCombineExponents.substitution(Mult(*(self.factors[:startIdx] + (dummyVar,) + self.factors[endIdx:])), dummyVar)
            return grouped.applyTransitivity(combineInGroup)
        if all(isinstance(factor, Sqrt) for factor in self.factors):
            # combine the square roots into one square root
            factorBases = [factor.base for factor in self.factors]
            return prodOfSqrts.specialize({xMulti:factorBases}, assumptions=assumptions)
        if len(self.operands) != 2 or not isinstance(self.operands[0], Exp) or not isinstance(self.operands[1], Exp):
            if len(self.operands) == 2 and isinstance(self.operands[0], Exp) and self.operands[0].base == self.operands[1]:
                # Of the form a^b a
                return addOneRightInExp.specialize({a:self.operands[1], b:self.operands[0].exponent}, assumptions=assumptions).deriveReversed(assumptions)
            elif len(self.operands) == 2 and isinstance(self.operands[1], Exp) and self.operands[1].base == self.operands[0]:
                # Of the form a a^b
                return addOneLeftInExp.specialize({a:self.operands[0], b:self.operands[1].exponent}, assumptions=assumptions).deriveReversed(assumptions)
            raise Exception('Combine exponents only implemented for a product of two exponentiated operands (or a simple variant)')
        if self.operands[0].base == self.operands[1].base:
            # Same base: a^b a^c = a^{b+c}$, or something similar
            aSub = self.operands[0].base
            bSub = self.operands[0].exponent
            if isinstance(self.operands[1].exponent, Neg):
                # equate $a^b a^{-c} = a^{b-c}$
                thm = diffInExp
                cSub = self.operands[1].exponent.operand
            elif isinstance(self.operands[1].exponent, Div) and isinstance(self.operands[1].exponent.numerator, Neg):
                # equate $a^b a^{-c/d} = a^{b-c/d}$
                thm = diffFracInExp
                cSub = self.operands[1].exponent.numerator.operand
                dSub = self.operands[1].exponent.denominator
                return thm.specialize({a:aSub, b:bSub, c:cSub, d:dSub}, assumptions=assumptions)
            else:
                # standard $a^b a^c = a^{b+c}$
                thm = sumInExp
                cSub = self.operands[1].exponent
        elif self.operands[0].exponent == self.operands[1].exponent:
            # Same exponent: equate $a^c b^c = (a b)^c$
            aSub = self.operands[0].base
            bSub = self.operands[1].base
            expSub = self.operands[0].exponent
            try:
                return natsPosExpOfProd.specialize({n:expSub}, assumptions=assumptions).deriveReversed(assumptions).specialize({a:aSub, b:bSub}, assumptions=assumptions)
            except:
                pass
            try:
                return intExpOfProd.specialize({n:expSub}, assumptions=assumptions).deriveReversed(assumptions).specialize({a:aSub, b:bSub}, assumptions=assumptions)
            except:
                return expOfPositivesProd.specialize({c:expSub}, assumptions=assumptions).deriveReversed(assumptions).specialize({a:aSub, b:bSub}, assumptions=assumptions)
        else:
            raise Exception('Product is not in the correct form to combine exponents: ' + str(self))
        return thm.specialize({a:aSub, b:bSub, c:cSub}, assumptions=assumptions).deriveReversed(assumptions)

    def commutation(self, initIdx=None, finalIdx=None, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operand
        at index initIdx has been moved to finalIdx.
        For example, (a + b + ... + y + z) = (a + ... + y + b + z)
        via initIdx = 1 and finalIdx = -2.
        '''
        from ._theorems_ import commutation, leftwardCommutation, rightwardCommutation
        return apply_commutation_thm(self, initIdx, finalIdx, commutation, leftwardCommutation, rightwardCommutation, assumptions)

    def groupCommutation(self, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operands
        at indices [initIdx, initIdx+length) have been moved to [finalIdx. finalIdx+length).
        It will do this by performing association first.  If disassocate is True, it
        will be disassociated afterwards.
        '''
        return groupCommutation(self, initIdx, finalIdx, length, disassociate, assumptions)
        
    def association(self, startIdx, length, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which operands in the
        range [startIdx, startIdx+length) are grouped together.
        For example, (a + b + ... + y + z) = (a + b ... + (l + ... + m) + ... + y + z)
        '''
        from ._theorems_ import association
        return apply_association_thm(self, startIdx, length, association, assumptions)

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        '''
        Given numerical operands, deduce that this expression is equal to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a + b ... + (l + ... + m) + ... + y+ z) = (a + b + ... + y + z)
        '''
        from ._theorems_ import disassociation
        return apply_disassociation_thm(self, idx, disassociation, assumptions)



class InnerMultiplication(DistributiveInnerExprMixin, CommutativeAndAssociativeInnerExprMixin, InnerExprMethodsObject):
    def __init__(self, innerExpr):
        InnerExprMethodsObject.__init__(self, innerExpr)
        if not isinstance(self.expr, Mult):
            raise TypeError("InnerMultiplication is expecting an Mult object as the inner expression")
