from proveit import Literal, Operation, USE_DEFAULTS, ProofFailure, tryDerivation, defaults
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.common import A, x, y, S

NOT = Literal(__package__, stringFormat = 'not', latexFormat = r'\lnot')

class Not(Operation):
    def __init__(self, A):
        Operation.__init__(self, NOT, A)
        self.operand = A

    def deriveSideEffects(self, knownTruth):
        '''
        From :math:`\lnot A` derive :math:`A = \bot` and :math:`A \Rightarrow \bot` as a side-effects.
        If this happens to be of the form :math:`\lnot \lnot A`, derive :math:`A`.
        If this happens to be of the form :math:`\lnot(A = B)`, derive :math:`A \neq B`.
        If this happens to be of the form :math:`\lnot(x \in S)`, derive :math:`x \nin S`.
        If this happens to be of the form :math:`\lnot(\exists ...)`, derive :math:`\nexists ...`.
        '''
        from proveit.logic import Equals, InSet, Exists
        if self.operand != FALSE: # avoid infinite recursion
            tryDerivation(self.equateNegatedToFalse, knownTruth.assumptions)
        tryDerivation(self.deriveContradiction, knownTruth.assumptions)
        if isinstance(self.operand, Not):
            tryDerivation(self.deriveViaDoubleNegation, knownTruth.assumptions)
        if isinstance(self.operand, Equals):
            tryDerivation(self.deriveNotEquals, knownTruth.assumptions)
        if isinstance(self.operand, InSet):
            tryDerivation(self.deriveNotIn, knownTruth.assumptions)
        if isinstance(self.operand, Exists):
            tryDerivation(self.deriveNotExists, knownTruth.assumptions)
    
    def conclude(self, assumptions):
        '''
        Try to automatically conclude this negation via evaluation reductions
        or double negation.
        '''
        # as a last resort (concludeNegation on the operand should have been
        # tried first), conclude negation via evaluating the operand as false.
        self.operand.evaluate(assumptions=assumptions)
        return self.concludeViaFalsifiedNegation(assumptions=assumptions)
    
    def concludeNegation(self, assumptions):
        '''
        Try to conclude the negation of this negation via double negation.  That
        is, conclude Not(Not(A)), where self=Not(A), via proving A.
        If that fails (e.g., an unusable theorem), call conclude on
        Not(Not(A)) directly.
        '''
        try:
            return Not(self).concludeViaDoubleNegation(assumptions)
        except:
            return Not(self).conclude(assumptions)
            
    @classmethod
    def operatorOfOperation(subClass):
        return NOT
    
    def latex(self, fence=False):
        outStr = ''
        if fence: outStr += "("
        outStr += self.operator.latex() + ' ' + self.operand.latex(fence=True)
        if fence: outStr += ')'
        return outStr            
    
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Given an operand that evaluates to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from _theorems_ import notT, notF # load in truth-table evaluations
        from _theorems_ import doubleNegationEquiv
        from proveit.logic.boolean.negation._axioms_ import falsifiedNegationIntro
        if self.operand == TRUE: return notT
        if self.operand == FALSE: return notF
        opValue = self.operand.evaluate(assumptions=assumptions).rhs
        if opValue == TRUE:
            # evaluate to FALSE via falsifiedNegationIntro
            return falsifiedNegationIntro.specialize({A:self.operand}, assumptions=assumptions)
        return Operation.evaluate(self, assumptions)
    
    def substituteInFalse(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        Given Not(A), derive P(False) from P(A).
        '''
        from proveit.logic.equality._theorems_ import substituteInFalse
        from proveit.logic import Equals
        from proveit.common import P
        Plambda = Equals._lambdaExpr(lambdaMap, self.operand)
        return substituteInFalse.specialize({x:self.operand, P:Plambda}, assumptions=assumptions)            

    def substituteFalsehood(self, lambdaMap, assumptions=USE_DEFAULTS):
        '''
        Given Not(A), derive P(A) from P(False).
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
        from _theorems_ import closure
        return closure.specialize({A:self.operand}, assumptions=assumptions)
   
    def equateNegatedToFalse(self, assumptions=USE_DEFAULTS):
        r'''
        From Not(A), derive and return A = FALSE.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from _axioms_ import negationElim
        return negationElim.specialize({A:self.operand}, assumptions=assumptions)
    
    def doubleNegationEquivalence(self, assumptions=USE_DEFAULTS):
        r'''
        Given Not(Not(A)), deduce and return Not(Not(A)) = A.
        '''
        from _theorems_ import doubleNegationEquiv
        if isinstance(self.operand, Not):
            return doubleNegationEquiv.specialize({A:self.operand.operand}, assumptions=assumptions)
        raise ValueError("doubleNegationEquivalence does not apply to " + str(self) + " which is not of the form Not(Not(A))")
    
    def deriveViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        From Not(Not(A)), derive and return A.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from _theorems_ import fromDoubleNegation
        if isinstance(self.operand, Not):
            return fromDoubleNegation.specialize({A:self.operand.operand}, assumptions=assumptions)
        raise ValueError("deriveViaDoubleNegation does not apply to " + str(self) + " which is not of the form Not(Not(A))")

    def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        Prove and return self of the form Not(Not(A)) assuming A.
        Also see version in NotEquals for A != FALSE.
        '''
        from _theorems_ import toDoubleNegation
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return toDoubleNegation.specialize({A:stmt}, assumptions=assumptions)

    def concludeViaFalsifiedNegation(self, assumptions=USE_DEFAULTS):
        r'''
        Prove and return self of the from not(A) assuming A=FALSE.
        '''
        from _axioms_ import negationIntro
        return negationIntro.specialize({A:self.operand}, assumptions=assumptions)                        
            
    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        r'''
        From not(A), and assuming A, derive and return FALSE.
        '''
        from _theorems_ import negationContradiction
        return negationContradiction.specialize({A:self.operand}, assumptions=assumptions)
    
    def affirmViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From Not(A), derive the conclusion provided that the negated conclusion
        implies both Not(A) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.boolean.implication import affirmViaContradiction
        return affirmViaContradiction(self, conclusion, assumptions)
    
    def deriveNotEquals(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot(A = B)`, derive and return :math:`A \neq B`.
        '''
        from proveit.logic import Equals
        from proveit.logic.equality._theorems_ import foldNotEquals
        if isinstance(self.operand, Equals):
            return foldNotEquals.specialize({x:self.operand.lhs, y:self.operand.rhs}, assumptions=assumptions)

    def deriveNotIn(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot(A \in B)`, derive and return :math:`A \notin B`.
        '''
        from proveit.logic import InSet
        from proveit.logic.set_theory._theorems_ import foldNotIn
        if isinstance(self.operand, InSet):
            return foldNotIn.specialize({x:self.operand.element, S:self.operand.domain}, assumptions=assumptions)

    def deriveNotExists(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot \exists_{x | Q(x)} P(x)`, derive and return :math:`\nexists_{x | Q(x)} P(x)`
        '''
        from proveit.logic import Exists, NotExists
        operand = self.operand
        if isinstance(operand, Exists):
            existsExpr = operand
            notExistsExpr = NotExists(existsExpr.instanceVars, existsExpr.instanceExpr, domain=existsExpr.domain, conditions=existsExpr.conditions)
            return notExistsExpr.concludeAsFolded(assumptions)
        
    def deduceDoubleNegationEquiv(self, assumptions=USE_DEFAULTS):
        '''
        For some :math:`\lnot \lnot A`, derive and return :math:`A = \lnot \lnot A` assuming :math:`A \in mathbb{B}`.
        '''
        from _theorems_ import doubleNegationEquiv
        if isinstance(self.operand, Not):
            Asub = self.operand.operand
            return doubleNegationEquiv.specialize({A:Asub}, assumptions=assumptions)
