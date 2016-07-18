from proveit import Literal, Operation, maybeFencedString
from proveit.number.set import zero, one

EXPONENTIATE = Literal(__package__, 'EXPONENTIATE')

class Exp(Operation):
    def __init__(self, base, exponent):
        r'''
        Raise base to exponent power.
        '''
        Operation.__init__(self,EXPONENTIATE, (base, exponent))
        self.base = base
        self.exponent = exponent

    @classmethod
    def operatorOfOperation(subClass):
        return EXPONENTIATE

    def _closureTheorem(self, numberSet):
        import natural.theorems
        import real.theorems
        import complex.theorems
        from proveit.number import two
        if numberSet == NaturalsPos:
            return natural.theorems.powClosure
        elif numberSet == Reals:
            return real.theorems.powClosure
        elif numberSet == RealsPos:
            if self.exponent != two: # otherwise, use deduceInRealsPosDirectly(..)
                return real.theorems.powPosClosure            
        elif numberSet == Complexes:
            return complex.theorems.powClosure
    
    def simplification(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one exponent or zero or one base,
        derive and return this exponential expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from theorems import expZeroEqOne, exponentiatedZero, exponentiatedOne
        from theorems import expOne
        if self.exponent == zero:
            deduceInComplexes(self.base, assumptions)
            deduceNotZero(self.base, assumptions)
            return expZeroEqOne.specialize({a:self.base})
        elif self.exponent == one:
            return expOne.specialize({a:self.base})
        elif self.base == zero:
            deduceInComplexes(self.exponent, assumptions)
            deduceNotZero(self.exponent, assumptions)
            return exponentiatedZero.specialize({x:self.exponent})
        elif self.base == one:
            deduceInComplexes(self.exponent, assumptions)
            return exponentiatedOne.specialize({x:self.exponent})
        else:
            raise ValueError('Only trivial simplification is implemented (zero or one for the base or exponent)')

    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one exponent or zero or one base,
        derive this exponential expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
    def deduceInRealsPosDirectly(self, assumptions=frozenset()):
        import real.theorems
        from number import two
        if self.exponent == two:
            deduceInReals(self.base, assumptions)
            deduceNotZero(self.base, assumptions)
            return real.theorems.sqrdClosure.specialize({a:self.base}).checked(assumptions)
        # only treating certain special case(s) in this manner
        raise DeduceInNumberSetException(self, RealsPos, assumptions)

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.powNotEqZero

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
            
    def formatted(self, formatType, **kwargs):
        inner_str = self.base.formatted(formatType, forceFence=True)+r'^{'+self.exponent.formatted(formatType, fence=False) + '}'
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False        
        return maybeFencedString(inner_str, **kwargs)
    
    def distributeExponent(self, assumptions=frozenset()):
        from proveit.number import Fraction
        from proveit.number.division.theorems import fracIntExpRev, fracNatPosExpRev
        if isinstance(self.base, Fraction):
            exponent = self.exponent
            try:
                deduceInNaturalsPos(exponent, assumptions)
                deduceInComplexes([self.base.numerator, self.base.denominator], assumptions)
                deduceNotZero(self.base.denominator, assumptions)
                return fracNatPosExpRev.specialize({n:exponent}).specialize({a:self.numerator.base, b:self.denominator.base})
            except:
                deduceInIntegers(exponent, assumptions)
                deduceInComplexes([self.base.numerator, self.base.denominator], assumptions)
                deduceNotZero(self.base.numerator, assumptions)
                deduceNotZero(self.base.denominator, assumptions)
                return fracIntExpRev.specialize({n:exponent}).specialize({a:self.base.numerator, b:self.base.denominator})
        raise Exception('distributeExponent currently only implemented for a fraction base')
        
    def raiseExpFactor(self, expFactor, assumptions=frozenset()):
        from proveit.number import Neg
        from theorems import intExpOfExp, intExpOfNegExp
        if isinstance(self.exponent, Neg):
            b_times_c = self.exponent.operand
            thm = intExpOfNegExp
        else:
            b_times_c = self.exponent
            thm = intExpOfExp
        if not hasattr(b_times_c, 'factor'):
            raise Exception('Exponent not factorable, may not raise the exponent factor.')
        factorEq = b_times_c.factor(expFactor, pull='right', groupRemainder=True, assumptions=assumptions)
        if factorEq.lhs != factorEq.rhs:
            # factor the exponent first, then raise this exponent factor
            factoredExpEq = factorEq.substitution(self)
            return factoredExpEq.applyTransitivity(factoredExpEq.rhs.raiseExpFactor(expFactor, assumptions=assumptions))
        nSub = b_times_c.operands[1]
        aSub = self.base
        bSub = b_times_c.operands[0]
        deduceNotZero(aSub, assumptions)
        deduceInIntegers(nSub, assumptions)
        deduceInComplexes([aSub, bSub], assumptions)
        return thm.specialize({n:nSub}).specialize({a:aSub, b:bSub}).deriveReversed()

    def lowerOuterExp(self, assumptions=frozenset()):
        from proveit.number import Neg
        from theorems import intExpOfExp, intExpOfNegExp, negIntExpOfExp, negIntExpOfNegExp
        if not isinstance(self.base, Exp):
            raise Exception('May only apply lowerOuterExp to nested Exp operations')
        if isinstance(self.base.exponent, Neg) and isinstance(self.exponent, Neg):
            b_, n_ = self.base.exponent.operand, self.exponent.operand
            thm = negIntExpOfNegExp
        elif isinstance(self.base.exponent, Neg):
            b_, n_ = self.base.exponent.operand, self.exponent
            thm = intExpOfNegExp
        elif isinstance(self.exponent, Neg):
            b_, n_ = self.base.exponent, self.exponent.operand
            thm = negIntExpOfExp
        else:
            b_, n_ = self.base.exponent, self.exponent
            thm = intExpOfExp
        a_ = self.base.base
        deduceNotZero(self.base.base, assumptions)
        deduceInIntegers(n_, assumptions)
        deduceInComplexes([a_, b_], assumptions)
        return thm.specialize({n:n_}).specialize({a:a_, b:b_})
    
