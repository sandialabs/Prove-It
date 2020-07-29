from proveit import Literal, Operation, USE_DEFAULTS, ProofFailure
from proveit.logic.boolean.booleans import inBool
from proveit._common_ import A, x, y, S

class Not(Operation):
    # operator of the Not operation
    _operator_ = Literal(stringFormat='not', latexFormat=r'\lnot', context=__file__)
    
    def __init__(self, A):
        Operation.__init__(self, Not._operator_, A)
    
    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically.
        '''
        from proveit.logic import FALSE, Equals
        if self.operand != FALSE: # avoid infinite recursion
            yield self.equateNegatedToFalse # A=FALSE given Not(A)
        if not isinstance(self.operand, Equals): # avoid infinite recursion
            yield self.deriveUntrue # A != TRUE given Not(A)
        if isinstance(self.operand, Not):
            yield self.deriveViaDoubleNegation # A given Not(Not(A))
        try:
            try:
                self.operand.prove(automation=False)
                # derive FALSE given Not(A) and A
                yield self.deriveContradiction
            except ProofFailure:
                pass
        except:
            pass # no contradiction
        yield self.deriveInBool # [Not(A) in Boolean] given Not(A)
        if hasattr(self.operand, 'negationSideEffects'):
            # derive negation side-effects for the specific type of
            # expression being negated.
            for negSideEffect in self.operand.negationSideEffects(knownTruth):
                yield negSideEffect
            
    def inBoolSideEffects(self, knownTruth):
        '''
        From not(A) in Booleans deduce A in Booleans, where self is not(A).
        '''
        yield self.deduceOperandInBool
        
    def deriveInBool(self, assumptions=USE_DEFAULTS):
        '''
        From Not(A) derive [Not(A) in Booleans].
        '''
        return inBool(self).prove(assumptions=assumptions)
    
    def conclude(self, assumptions):
        '''
        Try to automatically conclude this negation via evaluation reductions
        or double negation.
        '''
        from proveit.logic import SimplificationError
        # as a last resort (concludeNegation on the operand should have been
        # tried first), conclude negation via evaluating the operand as false.
        try:
            self.operand.evaluation(assumptions=assumptions)
        except SimplificationError:
            raise ProofFailure(self, assumptions, "Unable to evaluate %s"%str(self.operand))
        return self.concludeViaFalsifiedNegation(assumptions=assumptions)
    
    def concludeNegation(self, assumptions):
        '''
        Try to conclude the negation of this negation via double negation.  That
        is, conclude not(not(A)), where self=not(A), via proving A.
        If that fails (e.g., an unusable theorem), call conclude on
        not(not(A)) directly.
        '''
        try:
            return Not(self).concludeViaDoubleNegation(assumptions)
        except:
            return Not(self).conclude(assumptions)
    
    def latex(self, fence=False, **kwargs):
        outStr = ''
        if fence: outStr += "("
        outStr += self.operator.latex() + ' ' + self.operand.latex(fence=True)
        if fence: outStr += ')'
        return outStr            
    
    def evaluation(self, assumptions=USE_DEFAULTS, *, automation=True,
                   **kwargs):
        '''
        Given an operand that evaluates to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from ._theorems_ import notT, notF # load in truth-table evaluations
        return Operation.evaluation(self, assumptions, automation=automation)
    
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        from ._theorems_ import notT
        from proveit.logic.boolean._common_ import TRUE, FALSE
        from proveit.logic.boolean.negation._theorems_ import falsifiedNegationIntro
        if self.operand == TRUE:
            assert not notT.isUsable(), "We should not get to here if notT is usable"
            # evaluate to FALSE via falsifiedNegationIntro
            return falsifiedNegationIntro.specialize({A:self.operand}, assumptions=assumptions)
    
    def substituteInFalse(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        Given not(A), derive P(False) from P(A).
        '''
        from proveit.logic.equality._theorems_ import substituteInFalse
        from proveit.logic import Equals
        from proveit._common_ import P
        Plambda = Equals._lambdaExpr(lambdaMap, self.operand)
        return substituteInFalse.specialize({x:self.operand, P:Plambda}, assumptions=assumptions)            

    def substituteFalsehood(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        Given not(A), derive P(A) from P(False).
        '''
        from proveit.logic.equality._theorems_ import substituteFalsehood
        from proveit.logic import Equals
        from proveit.common import P
        Plambda = Equals._lambdaExpr(lambdaMap, self.operand)
        return substituteFalsehood.specialize({x:self.operand, P:Plambda}, assumptions=assumptions)            
                
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'not' expression is in the set of BOOLEANS.
        '''
        from ._theorems_ import closure, doubleNegClosure
        if isinstance(self.operand, Not):
            return doubleNegClosure.specialize({A:self.operand.operand}, assumptions=assumptions)
        return closure.specialize({A:self.operand}, assumptions=assumptions)

    def deduceOperandInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that the negated operand is in the set of BOOLEANS.
        '''
        from ._theorems_ import operandInBool
        return operandInBool.specialize({A:self.operand}, assumptions=assumptions)
          
    def equateNegatedToFalse(self, assumptions=USE_DEFAULTS):
        r'''
        From not(A), derive and return A = FALSE.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from ._axioms_ import negationElim
        return negationElim.specialize({A:self.operand}, assumptions=assumptions)

    def deriveUntrue(self, assumptions=USE_DEFAULTS):
        r'''
        From not(A), derive and return A != TRUE.
        '''
        from ._theorems_ import untrueFromNegation
        return untrueFromNegation.specialize({A:self.operand}, assumptions=assumptions)    
        
    def doubleNegationEquivalence(self, assumptions=USE_DEFAULTS):
        r'''
        Given not(not(A)), deduce and return not(not(A)) = A.
        '''
        from ._theorems_ import doubleNegationEquiv
        if isinstance(self.operand, Not):
            return doubleNegationEquiv.specialize({A:self.operand.operand}, assumptions=assumptions)
        raise ValueError("doubleNegationEquivalence does not apply to " + str(self) + " which is not of the form not(not(A))")
    
    def deriveViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        From not(not(A)), derive and return A.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from ._axioms_ import doubleNegationElim
        if isinstance(self.operand, Not):
            return doubleNegationElim.specialize({A:self.operand.operand}, assumptions=assumptions)
        raise ValueError("deriveViaDoubleNegation does not apply to " + str(self) + " which is not of the form not(not(A))")

    def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        Prove and return self of the form not(not(A)) assuming A.
        Also see version in NotEquals for A != FALSE.
        '''
        from ._axioms_ import doubleNegationIntro
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return doubleNegationIntro.specialize({A:stmt}, assumptions=assumptions)

    def concludeViaFalsifiedNegation(self, assumptions=USE_DEFAULTS):
        r'''
        Prove and return self of the form not(A) assuming A=FALSE.
        '''
        from ._axioms_ import negationIntro
        return negationIntro.specialize({A:self.operand}, assumptions=assumptions)                        
            
    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        r'''
        From not(A), and assuming A, derive and return FALSE.
        '''
        from ._theorems_ import negationContradiction
        return negationContradiction.specialize({A:self.operand}, assumptions=assumptions)
    
    def affirmViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From not(A), derive the conclusion provided that the negated conclusion
        implies both not(A) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.boolean.implication import affirmViaContradiction
        return affirmViaContradiction(self, conclusion, assumptions)

    def denyViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From not(A), derive the negated conclusion provided that the conclusion
        implies both not(A) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.boolean.implication import denyViaContradiction
        return denyViaContradiction(self, conclusion, assumptions)
                        
    def deduceDoubleNegationEquiv(self, assumptions=USE_DEFAULTS):
        '''
        For some not(not(A)), derive and return A = not(not(A)) assuming A in Booleans.
        '''
        from ._theorems_ import doubleNegationEquiv
        if isinstance(self.operand, Not):
            Asub = self.operand.operand
            return doubleNegationEquiv.specialize({A:Asub}, assumptions=assumptions)


