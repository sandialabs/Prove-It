from proveit import (Literal, maybeFencedLatex, Operation, StyleOptions,
                     USE_DEFAULTS)
from proveit import TransRelUpdater
from proveit._common_ import x, y, z

class Div(Operation):
    # operator of the Add operation
    _operator_ = Literal(stringFormat='/', latexFormat= r'\div', context=__file__)    
    
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands.
        '''
        Operation.__init__(self, Div._operator_, [operandA, operandB], styles={'division':'inline'})
        self.numerator = self.operands[0]
        self.denominator = self.operands[1]
    
    def styleOptions(self):
        options = StyleOptions(self)
        options.add('division', "'inline': uses '/'; 'fraction': numerator over the denominator")
        return options
    
    def latex(self, **kwargs):
        if self.getStyle('division')=='fraction':
            # only fence if forceFence=True (a fraction within an exponentiation is an example of when fencing should be forced)
            kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False        
            return maybeFencedLatex(r'\frac{'+self.numerator.latex()+'}{'+self.denominator.latex()+'}', **kwargs)
        else:
            return Operation.latex(self,**kwargs) # normal division
    
    def remakeConstructor(self):
        if self.getStyle('division') == 'fraction':
            return 'frac' # use a different constructor if using the fraction style
        return Operation.remakeConstructor(self)


    def doReducedSimplification(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Perform simplifications of a Divide expression after the 
        operands have individually been simplified.  
        Cancels common factors...
        '''        
        expr = self
        eq = TransRelUpdater(expr, assumptions) # for convenience updating our equation
        
        # perform cancelations where possible
        expr = eq.update(expr.cancelations(assumptions))
        if not isinstance(expr, Div):
            # complete cancelation.
            return eq.relation
        
        return eq.relation

    def combineExponents(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import fracIntExp, fracNatPosExp
        from proveit.number import Exp
        if isinstance(self.numerator, Exp) and isinstance(self.denominator, Exp):
            if self.numerator.exponent == self.denominator.exponent:
                exponent = self.numerator.exponent
                try:
                    return fracNatPosExp.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
                except:
                    return fracIntExp.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
        raise Exception('Unable to combine exponents of this fraction')

    def cancelations(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        all simple division cancellations are performed.
        '''
        from proveit.number import Mult
        expr = self
        
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)
        
        num_factors = (self.numerator.operands if
                       isinstance(self.numerator, Mult) else 
                       [self.numerator])
        denom_factors = (self.denominator.operands if
                         isinstance(self.denominator, Mult) else 
                         [self.denominator])
        for num_factor in num_factors:
            if num_factor in denom_factors:
                expr = eq.update(expr.cancelation(num_factor, assumptions))
                denom_factors.pop(denom_factors.index(num_factor))
        
        return eq.relation    
    
    def cancelation(self, operand, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        the given operand has been canceled on the numerator and
        denominator.  For example,
        [(a*b)/(b*c)].cancelation(b) would return
        (a*b)/(b*c) = a / c
        '''        
        from proveit.number import Mult
        expr = self
        eq = TransRelUpdater(expr, assumptions)
        
        if self.numerator == self.denominator == operand:
            # x/x = 1
            from ._theorems_ import fracCancelComplete
            return fracCancelComplete.specialize({x:operand}).checked(assumptions)
        
        if operand != self.numerator:
            if (not isinstance(self.numerator, Mult) or
                    operand not in self.numerator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 %(operand, self))            
            # Factor the operand from the numerator to the left.
            expr = eq.update(expr.innerExpr().numerator.factorization(
                    operand, groupFactor=True, groupRemainder=True,
                    assumptions=assumptions))
        if operand != self.denominator:
            if (not isinstance(self.denominator, Mult) or
                    operand not in self.denominator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 %(operand, self))            
            # Factor the operand from the denominator to the left.
            expr = eq.update(expr.innerExpr().denominator.factorization(
                    operand, groupFactor=True, groupRemainder=True,
                    assumptions=assumptions))
        if operand == self.numerator:
            from ._theorems_ import fracCancelNumerLeft
            assert len(expr.denominator.operands) == 2, "Should be grouped"
            expr = eq.update(fracCancelNumerLeft.instantiate(
                    {x:operand,y:expr.denominator.operands[1]},
                    assumptions=assumptions))
            return eq.relation
        elif operand == self.denominator:
            from ._theorems_ import fracCancelDenomLeft
            assert len(expr.numerator.operands) == 2, "Should be grouped"
            expr = eq.update(fracCancelDenomLeft.instantiate(
                    {x:operand,y:expr.numerator.operands[1]},
                    assumptions=assumptions))
            return eq.relation
        else:
            from ._theorems_ import fracCancelLeft
            expr = eq.update(fracCancelLeft.instantiate(
                    {x:operand,y:expr.numerator.operands[1],
                     z:expr.denominator.operands[1]}, 
                     assumptions=assumptions))
            return eq.relation


    def distribution(self, assumptions=USE_DEFAULTS):
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
        from proveit.number import Add, subtract, Sum
        from ._theorems_ import distributefracThroughSum, distributefracThroughSubtract, distributefracThroughSummation
        if isinstance(self.numerator, Add):
            return distributefracThroughSum.specialize({xEtc:self.numerator.operands, y:self.denominator})
        elif isinstance(self.numerator, subtract):
            return distributefracThroughSubtract.specialize({x:self.numerator.operands[0], y:self.numerator.operands[1], z:self.denominator})
        elif isinstance(self.numerator, Sum):
            # Should deduce in Complexes, but distributeThroughSummation doesn't have a domain restriction right now
            # because this is a little tricky.   To do.
            #deduceInComplexes(self.operands, assumptions)
            yEtcSub = self.numerator.indices
            Pop, Pop_sub = Operation(P, self.numerator.indices), self.numerator.summand
            S_sub = self.numerator.domain
            dummyVar = safeDummyVar(self)            
            spec1 = distributefracThroughSummation.specialize({Pop:Pop_sub, S:S_sub, yEtc:yEtcSub, z:dummyVar})
            return spec1.deriveConclusion().specialize({dummyVar:self.denominator})
        else:
            raise Exception("Unsupported operand type to distribute over: " + self.numerator.__class__)
    
    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem.
        Created: 2/27/2020 by wdc, based on the same method in the Add
                 class. Just a start on this method, to be cont'd.
        Last Modified: 2/27/2020 by wdc. Creation.
        Once established, these authorship notations can be deleted.
        '''
        from proveit._common_ import a, b
        from proveit.number.division._theorems_ import (divRealClosure,
                                                        divideRealPosClosure,
                                                        divideComplexClosure)
        from proveit.number import Reals, RealsPos, Complexes

        if number_set == Reals:
            return divRealClosure.specialize(
                {a:self.numerator, b:self.denominator},
                assumptions=assumptions)
        elif number_set == RealsPos:
            return divideRealPosClosure.specialize(
                {a:self.numerator, b:self.denominator},
                assumptions=assumptions)
        elif number_set == Complexes:
            return divideComplexClosure.specialize(
                {a:self.numerator, b:self.denominator},
                assumptions=assumptions)

    """
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
        from ._theorems_ import fracInProdRev, prodOfFracsRev, prodOfFracsLeftNumerOneRev, prodOfFracsRightNumerOneRev
        from proveit.number import Mult, num
        dummyVar = safeDummyVar(self)
        eqns = []
        if isinstance(theFactor, frac):
            # factor the operand denominator out of self's denominator
            denomFactorEqn = self.denominator.factor(theFactor.denominator, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
            factoredDenom = denomFactorEqn.rhs
            eqns.append(denomFactorEqn.substitution(frac(self.numerator, dummyVar), dummyVar))
            if theFactor.numerator != num(1) and self.numerator != num(1):
                # factor the operand numerator out of self's numerator
                numerFactorEqn = self.numerator.factor(theFactor.numerator, pull, groupFactor=True, groupRemainder=True, assumptions=assumptions)
                factoredNumer = numerFactorEqn.rhs
                eqns.append(numerFactorEqn.substitution(frac(dummyVar, factoredDenom), dummyVar))
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
            eqns.append(numerFactorEqn.substitution(frac(dummyVar, self.denominator), dummyVar))
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
    """

def frac(numer, denom):
    return Div(numer, denom).withStyles(division='fraction')
