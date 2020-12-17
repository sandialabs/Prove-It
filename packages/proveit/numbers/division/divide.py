from proveit import (Literal, maybeFencedLatex, Operation, InnerExpr,
                     StyleOptions, USE_DEFAULTS)
from proveit import TransRelUpdater
from proveit._common_ import a, b, c, m, n, x, y, z

class Div(Operation):
    # operator of the Add operation
    _operator_ = Literal(stringFormat='/', latexFormat= r'\div', theory=__file__)    
    
    def __init__(self, numerator, denominator):
        r'''
        Divide two operands.
        '''
        Operation.__init__(self, Div._operator_, [numerator, denominator], 
                           styles={'division':'inline'})
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
        from proveit.numbers import one
        expr = self
        eq = TransRelUpdater(expr, assumptions) # for convenience updating our equation
        
        # perform cancelations where possible
        expr = eq.update(expr.cancelations(assumptions))
        if not isinstance(expr, Div):
            # complete cancelation.
            return eq.relation
        
        if self.denominator == one:
            # eliminate division by one
            eq.update(expr.eliminate_divide_by_one(assumptions))
            return eq.relation # no more division simplifications.
        
        return eq.relation
    
    """
    # outdated.  obsolete.
    def combineExponents(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import fracIntExp, fracNatPosExp
        from proveit.numbers import Exp
        if isinstance(self.numerator, Exp) and isinstance(self.denominator, Exp):
            if self.numerator.exponent == self.denominator.exponent:
                exponent = self.numerator.exponent
                try:
                    return fracNatPosExp.instantiate({n:exponent}).instantiate({a:self.numerator.base, b:self.denominator.base})
                except:
                    return fracIntExp.instantiate({n:exponent}).instantiate({a:self.numerator.base, b:self.denominator.base})
        raise Exception('Unable to combine exponents of this fraction')
    """

    def cancelations(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        all simple division cancellations are performed.
        '''
        from proveit.numbers import Mult
        expr = self
        
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)
        
        numer_factors = (self.numerator.operands if
                         isinstance(self.numerator, Mult) else 
                         [self.numerator])
        denom_factors = (self.denominator.operands if
                         isinstance(self.denominator, Mult) else 
                         [self.denominator])
        denom_factors_set = set(denom_factors)
        
        for numer_factor in numer_factors:
            if numer_factor in denom_factors_set:
                expr = eq.update(expr.cancelation(numer_factor, assumptions))
                denom_factors_set.remove(numer_factor)
        
        return eq.relation    
    
    def cancelation(self, term_to_cancel, assumptions=USE_DEFAULTS):
        '''
        Deduce and return an equality between self and a form in which
        the given operand has been canceled on the numerator and
        denominator.  For example,
        [(a*b)/(b*c)].cancelation(b) would return
        (a*b)/(b*c) = a / c
        '''        
        from proveit.numbers import Mult
        expr = self
        eq = TransRelUpdater(expr, assumptions)
        
        if self.numerator == self.denominator == term_to_cancel:
            # x/x = 1
            from ._theorems_ import fracCancelComplete
            return fracCancelComplete.instantiate({x:term_to_cancel}).checked(assumptions)
        
        if term_to_cancel != self.numerator:
            if (not isinstance(self.numerator, Mult) or
                    term_to_cancel not in self.numerator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 %(term_to_cancel, self))            
            # Factor the term_to_cancel from the numerator to the left.
            expr = eq.update(expr.innerExpr().numerator.factorization(
                    term_to_cancel, groupFactor=True, groupRemainder=True,
                    assumptions=assumptions))
        if term_to_cancel != self.denominator:
            if (not isinstance(self.denominator, Mult) or
                    term_to_cancel not in self.denominator.operands):
                raise ValueError("%s not in the denominator of %s"
                                 %(term_to_cancel, self))            
            # Factor the term_to_cancel from the denominator to the left.
            expr = eq.update(expr.innerExpr().denominator.factorization(
                    term_to_cancel, groupFactor=True, groupRemainder=True,
                    assumptions=assumptions))
        if term_to_cancel == self.numerator:
            from ._theorems_ import fracCancelNumerLeft
            assert len(expr.denominator.operands) == 2, "Should be grouped"
            expr = eq.update(fracCancelNumerLeft.instantiate(
                    {x:term_to_cancel,y:expr.denominator.operands[1]},
                    assumptions=assumptions))
            return eq.relation
        elif term_to_cancel == self.denominator:
            from ._theorems_ import fracCancelDenomLeft
            assert len(expr.numerator.operands) == 2, "Should be grouped"
            expr = eq.update(fracCancelDenomLeft.instantiate(
                    {x:term_to_cancel,y:expr.numerator.operands[1]},
                    assumptions=assumptions))
            return eq.relation
        else:
            from ._theorems_ import fracCancelLeft
            expr = eq.update(fracCancelLeft.instantiate(
                    {x:term_to_cancel,y:expr.numerator.operands[1],
                     z:expr.denominator.operands[1]}, 
                     assumptions=assumptions))
            return eq.relation
        
    def deepOneEliminations(self, assumptions=USE_DEFAULTS):
        '''
        Eliminate ones from the numerator, the denominator,
        and as a division by one.
        '''
        from proveit.numbers import one
        expr = self
        
        # A convenience to allow successive update to the equation 
        # via transitivities (starting with self=self).
        eq = TransRelUpdater(self, assumptions)
        
        for _i, operand in enumerate(self.operands):
            if hasattr(operand, 'deepOneEliminations'):
                expr = eq.update(expr.innerExpr().operands[_i]. \
                                 deepOneEliminations(assumptions))
        
        if expr.denominator == one:
            expr = eq.update(expr.eliminate_divide_by_one(assumptions))
        return eq.relation        
    
    def eliminate_divide_by_one(self, assumptions=USE_DEFAULTS):
        from proveit.numbers import one
        from ._theorems_ import fracOneDenom
        if self.denominator != one:
            raise ValueError("'eliminate_divide_by_one' is only applicable "
                             "if the denominator is precisely one.")
        return fracOneDenom.instantiate({x:self.numerator},
                                        assumptions=assumptions)

    def distribution(self, assumptions=USE_DEFAULTS):
        r'''
        Distribute the denominator through the numerate.  
        Returns the equality that equates self to this new version.
        Examples: 
            :math:`(a + b + c) / d = a / d + b / d + c / d`
            :math:`(a - b) / d = a / d - b / d`
            :math:`\left(\sum_x f(x)\right / y = \sum_x [f(x) / y]`
        Give any assumptions necessary to prove that the operands are in the Complex
        numbers so that the associative and commutation theorems are applicable.
        '''
        from proveit.numbers import Add, subtract, Sum
        from ._theorems_ import distributefracThroughSum, distributefracThroughSubtract, distributefracThroughSummation
        if isinstance(self.numerator, Add):
            return distributefracThroughSum.instantiate({xEtc:self.numerator.operands, y:self.denominator})
        elif isinstance(self.numerator, subtract):
            return distributefracThroughSubtract.instantiate({x:self.numerator.operands[0], y:self.numerator.operands[1], z:self.denominator})
        elif isinstance(self.numerator, Sum):
            # Should deduce in Complex, but distributeThroughSummation doesn't have a domain restriction right now
            # because this is a little tricky.   To do.
            #deduceInComplex(self.operands, assumptions)
            yEtcSub = self.numerator.indices
            Pop, Pop_sub = Operation(P, self.numerator.indices), self.numerator.summand
            S_sub = self.numerator.domain
            dummyVar = safeDummyVar(self)            
            spec1 = distributefracThroughSummation.instantiate({Pop:Pop_sub, S:S_sub, yEtc:yEtcSub, z:dummyVar})
            return spec1.deriveConclusion().instantiate({dummyVar:self.denominator})
        else:
            raise Exception("Unsupported operand type to distribute over: " + self.numerator.__class__)
    
    def exponentCombination(self, startIdx=None, endIdx=None,
                            assumptions=USE_DEFAULTS):
        '''
        Equates $a^m/a^n$ to $a^{m-n} or
        $a^c/b^c$ to $(a/b)^c$.
        '''
        from proveit.logic import InSet
        from proveit.numbers import (Exp, NaturalPos, RealPos, Real,
                                    Complex)
        from proveit.numbers.exponentiation._theorems_ import (
                quotient_of_posnat_powers, quotient_of_pos_powers,
                quotient_of_real_powers, quotient_of_complex_powers)
        if (isinstance(self.numerator, Exp) 
                and isinstance(self.denominator, Exp)):
            if self.numerator.base == self.denominator.base:
                # Same base: (a^b/a^c) = a^{b-c}
                same_base = self.numerator.bas
                exponents = (self.numerator.exponent, 
                             self.denominator.exponent)
                # Find out the known type of the exponents.
                possible_exponent_types = [NaturalPos, RealPos, Real,
                                           Complex]
                for exponent in exponents:
                    while len(possible_exponent_types) > 1:
                        exponent_type = possible_exponent_types[0]
                        if InSet(exponent, exponent_type).proven(assumptions):
                            # This type is known for this exponent.
                            break
                        # We've eliminated a type from being known. 
                        possible_exponent_types.pop(0)
                known_exponent_type = possible_exponent_types[0]
                
                if known_exponent_type==NaturalPos:
                    _m, _n = exponents
                    return quotient_of_posnat_powers.instantiate(
                            {a:same_base, m:_m, n:_n}, assumptions=assumptions)        
                else:
                    _b, _c = exponents
                    if known_exponent_type==RealPos:
                        thm = quotient_of_pos_powers
                    elif known_exponent_type==Real:
                        thm = quotient_of_real_powers
                    else: # Complex is the default
                        thm = quotient_of_complex_powers
                    thm.instantiate({a:same_base, b:_b, c:_c}, 
                                    assumptions=assumptions)
            
            elif self.numerator.exponent == self.denominator.exponent:
                # Same exponent: (a^c/b^c) = (a/b)^c
                same_exponent = self.numerator.exponent
                bases = (self.numerator.base, self.denominator.base)
                # Combining the exponents in this case is the reverse
                # of disibuting an exponent.
                quotient = Div(*bases).withMatchingStyle(self)
                exp = Exp(quotient, same_exponent)
                return exp.distribution(assumptions).deriveReversed(assumptions)    
        else:
            raise NotImplementedError("Need to implement degenerate cases "
                                      "of a^b/a and a/a^b.")            
        
    
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
        from proveit.numbers.division._theorems_ import (
                div_rational_closure, div_rational_non_zero_closure,
                div_rational_pos_closure, div_rational_non_neg_closure,
                divRealClosure, divideRealPosClosure, divideComplexClosure)
        from proveit.numbers import (
                Rational, RationalNonZero, RationalPos, RationalNonNeg,
                Real, RealPos, Complex)
        
        thm = None
        if number_set == Rational:
            thm = div_rational_closure
        elif number_set == RationalNonZero:
            thm = div_rational_non_zero_closure
        elif number_set == RationalPos:
            thm = div_rational_pos_closure
        elif number_set == RationalNonNeg:
            thm = div_rational_non_neg_closure
        elif number_set == Real:
            thm = divRealClosure
        elif number_set == RealPos:
            thm = divideRealPosClosure
        elif number_set == Complex:
            thm = divideComplexClosure
        if thm is not None:
            return thm.instantiate({a:self.numerator, b:self.denominator},
                                   assumptions=assumptions)

    """
    def factor(self,theFactor,pull="left", groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a factor from a fraction, pulling it either to the "left" or "right".
        The factor may be a product or fraction itself.  
        If groupFactor is True and theFactor is a product, it will be grouped together as a 
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in the Complex numbers so that
        the associative and commutation theorems are applicable.
        '''        
        from ._theorems_ import fracInProdRev, prodOfFracsRev, prodOfFracsLeftNumerOneRev, prodOfFracsRightNumerOneRev
        from proveit.numbers import Mult, num
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
                eqns.append(prodOfFracsRev.instantiate({x:factoredNumer.operands[0], y:factoredNumer.operands[1], 
                                                    z:factoredDenom.operands[0], w:factoredDenom.operands[1]}))
            else:
                # special case: one of the numerators is equal to one, no numerator factoring to be done
                if (pull == 'left') == (theFactor.numerator == num(1)):
                    thm = prodOfFracsLeftNumerOneRev
                else:
                    thm = prodOfFracsRightNumerOneRev
                # factor the two fractions
                eqns.append(thm.instantiate({x:self.numerator, y:factoredDenom.operands[0], z:factoredDenom.operands[1]}))
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
            eqns.append(fracInProdRev.instantiate({wEtc:wEtcSub, x:xSub, y:self.denominator, zEtc:zEtcSub}))
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

# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(Div, 'deepOneEliminations', 'deepEliminatedOnes', 'deepEliminateOnes')
InnerExpr.register_equivalence_method(Div, 'exponentCombination', 'combinedExponents', 'combineExponents')
