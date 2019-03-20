from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import a, b, c, x, y
from proveit.logic.irreducible_value import isIrreducibleValue
from proveit.number.numeral.deci import DIGITS
import proveit.number.numeral.deci._theorems_

class Add(Operation):
    # operator of the Add operation
    _operator_ = Literal(stringFormat='+', context=__file__)
    
    # Map terms to sets of KnownTruth equalities that involve
    # the term on the left hand side. 
    knownEqualities = dict()
    
    # Adding two numerals may import a theorem for the evaluation.
    # Track which ones we have encountered already.
    addedNumerals = set()
    
    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information under
        the Expression jurisdiction.  All Expression classes that store Prove-It
        state information must implement _clear_ to clear that information.
        '''
        Add.knownEqualities.clear()
        Add.addedNumerals.clear()
        
    def __init__(self, *operands):
        r'''
        Add together any number of operands.
        '''
        Operation.__init__(self, Add._operator_, operands)
        self.terms = self.operands
        if len(self.terms)==2 and all(term in DIGITS for term in self.terms):
            if self not in Add.addedNumerals:
                try:
                    # for single digit addition, import the theorem that provides the evaluation
                    Add.addedNumerals.add(self)
                    proveit.number.numeral.deci._theorems_.__getattr__('add_%d_%d'%(self.terms[0].asInt(), self.terms[1].asInt()))
                except:
                    # may fail before the relevent _commons_ and _theorems_ have been generated
                    pass # and that's okay
    
    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.addRealClosure
        elif numberSet == Complexes:
            return theorems.addComplexClosure
        elif numberSet == Integers:
            return theorems.addIntClosure
    
    def equalitySideEffects(self, knownTruth):
        '''
        Record the knownTruth in Add.knownEqualities, associated for
        each term.
        '''
        addition = knownTruth.lhs
        if not isinstance(addition, Add):
            raise ValueError("Expecting lhs of knownTruth to be of an Add expression")
        for term in addition.terms:
            Add.knownEqualities.setdefault(term, set()).add(knownTruth)
        if len(addition.terms)==2:
            # deduce the subtraction form: c-b=a from a+b=c 
            yield (lambda assumptions : self.deduceSubtraction(knownTruth.rhs, assumptions))

    def deduceSubtraction(self, rhs, assumptions=USE_DEFAULTS):
        '''
        From (a + b) = rhs, derive and return rhs - b = a.
        '''
        from proveit.number.subtraction._theorems_ import subtractFromAdd
        if len(self.terms) != 2:
            raise Exception("deduceSubtraction implemented only when there are two and only two added terms")
        deduction = subtractFromAdd.specialize({a:self.terms[0], b:self.terms[1], c:rhs}, assumptions=assumptions)
        return deduction
        
    """
    def simplification(self, assumptions=frozenset()):
        '''
        For the trivial case of a zero term,
        derive and return this Add expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from theorems import addZero
        eq = Equation()
        expr = self
        try:
            zeroIdx = expr.operands.index(zero)
            # there is a zero in the sum.  We can simplify that.
            if zeroIdx > 0:
                # commute it so that the zero comes first
                expr = eq.update(expr.commute(0, zeroIdx, zeroIdx, zeroIdx+1, assumptions)).rhs
            if len(expr.operands) > 2:
                # group the other operands so there are only two at the top level
                expr = eq.update(expr.group(1, len(expr.operands), assumptions)).rhs
            deduceInComplexes(expr.operands[1], assumptions)
            return eq.update(addZero.specialize({x:expr.operands[1]}))
        except ValueError:
            raise ValueError('Only trivial simplification is implemented (zero term)')
        
    def simplified(self, assumptions=frozenset()):
        '''
        For the trivial case of a zero term,
        derive this Add expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
    """
    
    def subtractionFolding(self, termIdx=None, assumptions=frozenset()):
        '''
        Given a negated term, termIdx or the first negated term if termIdx is None,
        deduce the equivalence between self and a Subtract form (with the specified
        negated term on the right of the subtraction).  Assumptions
        may be necessary to deduce operands being in the set of Complexes.
        '''
        from proveit.number import Neg
        from proveit.number.subtraction.theorems import addNegAsSubtract
        if termIdx is None:
            for k, term in enumerate(self.terms):
                if isinstance(term, Neg):
                    termIdx = k
                    break
            if termIdx is None:
                raise Exception("No negated term, can't provide the subtraction folding.")
        if not isinstance(self.terms[termIdx], Neg):
            raise ValueError("Specified term is not negated, can't provide the subtraction folding.")
        expr = self
        if termIdx != -1 and termIdx != len(expr.terms)-1:
            # put the negative term at the end
            expr = expr.commute(termIdx, termIdx+1, -1)
        if len(expr.terms) > 2:
            # group all of the other terms
            expr = expr.group(0, -1)
        deduceInComplexes(expr.operands[0], assumptions)
        deduceInComplexes(expr.operands[-1].operand, assumptions)
        return addNegAsSubtract.specialize({x:expr.operands[0], y:expr.operands[-1].operand})
    
    def deduceInNaturalsPosDirectly(self, assumptions=frozenset(), ruledOutSets=frozenset(), dontTryPos=False, dontTryNeg=False):
        '''
        If all of the terms are in Naturals and just one is positive, then the sum is positive.
        '''
        from numberSets import DeduceInNumberSetException
        from theorems import addNatPosClosure
        
        # first make sure all the terms are in Naturals
        for term in self.operands:
            deduceInNaturals(term, assumptions) 
        for k, term in enumerate(self.operands):
            try:
                # found one positive term to make the sum positive
                deducePositive(term, assumptions)
                return addNatPosClosure.specialize({aEtc:self.operands[:k], b:term, cEtc:self.operands[k+1:]}).checked(assumptions)
            except:
                pass
        # need to have one of the elements positive for the sum to be positive
        raise DeduceInNumberSetException(self, NaturalsPos, assumptions)

    def deduceStrictIncrease(self, lowerBoundTermIndex, assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealsPos, deduce an return
        the statement that the sum is greater than the term at lowerBoundTermIndex.
        Assumptions may be needed to deduce that the terms are in RealsPos or Reals.
        '''
        from theorems import strictlyIncreasingAdditions        
        for i, term in enumerate(self.terms):
            if i == lowerBoundTermIndex:
                deduceInReals(term, assumptions)
            else:
                deduceInRealsPos(term, assumptions)
        return strictlyIncreasingAdditions.specialize({aEtc:self.terms[:lowerBoundTermIndex], cEtc:self.terms[lowerBoundTermIndex+1:]}).specialize({b:self.terms[lowerBoundTermIndex]}).checked(assumptions)

    def deduceStrictDecrease(self, upperBoundTermIndex, assumptions=frozenset()):
        '''
        Deducing that all other terms are in RealsNeg, deduce an return
        the statement that the sum is less than the term at upperBoundTermIndex.
        Assumptions may be needed to deduce that the terms are in RealsPos or Reals.
        '''
        from theorems import strictlyDecreasingAdditions        
        for i, term in enumerate(self.terms):
            if i == upperBoundTermIndex:
                deduceInReals(term, assumptions)
            else:
                deduceInRealsNeg(term, assumptions)
        return strictlyDecreasingAdditions.specialize({aEtc:self.terms[:upperBoundTermIndex], cEtc:self.terms[upperBoundTermIndex+1:]}).specialize({b:self.terms[upperBoundTermIndex]}).checked(assumptions)
        
    def commute(self, startIdx1=None, endIdx1=None, startIdx2=None, endIdx2=None, assumptions=frozenset()):
        '''
        Commute self.operands[startIdx1:endIdx1] with self.operands[startIdx2:endIdx2].  
        The default, if no indices are provided, is to commute the first operand with the rest
        (convenient especially when there are just two operands).
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from theorems import addComm
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
        return addComm.specialize({vEtc:vSub, wEtc:wSub, xEtc:xSub, yEtc:ySub, zEtc:zSub}, assumptions=assumptions)
    
    def group(self, startIdx=None, endIdx=None, assumptions=frozenset()):
        '''
        Group together (associate as a sub-sum wrapped in parenthesis)
        consecutive operands, self.operands[startIdx:endIdx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        from axioms import addAssoc
        deduceInComplexes(self.operands, assumptions)
        xSub = self.operands[:startIdx] if startIdx is not None else []
        ySub = self.operands[startIdx:endIdx]
        zSub = self.operands[endIdx:] if endIdx is not None else []
        return addAssoc.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def ungroup(self, idx, assumptions=frozenset()):
        '''
        Ungroup (un-associate a sub-sum wrapped in parenthesis)
        an operand, self.operands[idx].
        Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in 
        Complexes so that the commutation theorem is applicable.
        '''
        if not isinstance(self.operands[idx], Add):  
            raise ValueError("Selected term is not an Add expression")

        from theorems import addAssocRev
        deduceInComplexes(self.operands, assumptions)
        deduceInComplexes(self.operands[idx].operands, assumptions)
        xSub = self.operands[:idx] if idx is not None else []
        ySub = self.operands[idx].operands
        zSub = self.operands[idx+1:] if idx is not None else []
        return addAssocRev.specialize({xEtc:xSub, yEtc:ySub, zEtc:zSub}).checked(assumptions)

    def factor(self, theFactor, pull="left", groupFactor=True, assumptions=frozenset()):
        '''
        Factor out "theFactor" from this sum, pulling it either to the "left" or "right".
        If groupFactor is True and theFactor is a product, these operands are grouped 
        together as a sub-product.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from proveit.number.multiplication.theorems import distributeThroughSumRev
        expr = self
        eq = Equation()
        dummyVar = self.safeDummyVar()
        yEtcSub = []
        for i, term in enumerate(self.terms):
            sumWithDummy = Add(*[jterm if j != i else dummyVar for j, jterm in enumerate(expr.terms)])
            termFactorization = term.factor(theFactor, pull, groupFactor=groupFactor, groupRemainder=True, assumptions=assumptions)
            if not isinstance(termFactorization.rhs, Multiply):
                raise Exception('Expecting right hand size of factorization to be a product')
            if pull == 'left':
                # the grouped remainder on the right
                yEtcSub.append(termFactorization.rhs.operands[-1]) 
            else:
                # the grouped remainder on the left
                yEtcSub.append(termFactorization.rhs.operands[0])
            eq.update(termFactorization.substitution(sumWithDummy, dummyVar))
            expr = eq.eqExpr.rhs
        if not groupFactor and isinstance(theFactor, Multiply):
            factorSub = theFactor.operands
        else:
            factorSub = [theFactor]
        deduceInComplexes(factorSub, assumptions=assumptions)
        deduceInComplexes(yEtcSub, assumptions=assumptions)
        if pull == 'left':
            xEtcSub = factorSub
            zEtcSub = []
        else:
            xEtcSub = []
            zEtcSub = factorSub
        eq.update(distributeThroughSumRev.specialize({xEtc:xEtcSub, yEtc:yEtcSub, zEtc:zEtcSub}))
        return eq.eqExpr.checked(assumptions)
    
    def join(self, assumptions=frozenset()):
        '''
        For joining two summations (could be more sophistocated later).
        '''
        from proveit.number import Sum
        if len(self.terms) != 2 or not all(isinstance(term, Sum) for term in self.terms):
            raise Exception("Sum joinoing currently only implemented for two summation terms.")
        return self.terms[0].join(self.terms[1], assumptions)
    
    """
    def evaluation(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that evaluate to numbers, derive and
        return the equality of this expression with the sum of these numbers. 
        '''
        from proveit.number.sets.integer._axioms_ import twoDef, threeDef, fourDef, fiveDef, sixDef, sevenDef, eightDef, nineDef # load in integer successor evaluations  
        for i, operand in enumerate(self.operands):
            if not isIrreducibleValue(operand):
                # The operands are not always true/false, so try the default evaluation method
                # which will attempt to evaluate each of the operands.
                return Operation.evaluation(self, assumptions)
        # TODO
        
        '''
        From disjunction, just brought in as an example
        if len(self.operands) == 2:
            # This will automatically return orTT, orTF, orFT, or orFF
            return Operation.evaluation(self, assumptions)
        if trueIndex >= 0:
            # one operand is TRUE so the whole disjunction evaluate to TRUE.
            return disjunctionTrueEval.specialize({Amulti:self.operands[:trueIndex], Cmulti:self.operands[trueIndex+1:]}, assumptions=assumptions)
        else:
            # no operand is TRUE so the whole disjunction evaluate to FALSE.
            return disjunctionFalseEval.specialize({Amulti:self.operands}, assumptions=assumptions)
        '''
    """