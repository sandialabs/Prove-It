from proveit import Literal, Operation, USE_DEFAULTS, ProofFailure, tryDerivation
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
        from _theorems_ import notFalse
        if self == notFalse.expr: return notFalse # simple special case
        if isinstance(self.operand, Not) and isinstance(self.operand.operand, Not):
            # try to conclude this as a double negation.  in fact,
            # the expression being double-negated must be true in order
            # for the double-negation to be true.
            return self.concludeViaDoubleNegation(assumptions)
        # conclude negation via evaluating the operand as false.
        self.operand.evaluate(assumptions=assumptions)
        return self.concludeViaFalsifiedNegation(assumptions=assumptions)
        
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
        from proveit.logic.boolean.negation._axioms_ import falsifiedNegationIntro
        opValue = self.operand.evaluate(assumptions=assumptions).rhs
        if opValue == TRUE:
            # evaluate to FALSE via falsifiedNegationIntro
            return falsifiedNegationIntro.specialize({A:self.operand}, assumptions=assumptions)
        return Operation.evaluate(self, assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'not' expression is in the set of BOOLEANS.
        '''
        from _theorems_ import negationClosure
        return negationClosure.specialize({A:self.operand}, assumptions=assumptions)
   
    def equateNegatedToFalse(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot A`, derive and return :math:`A = \bot`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from _axioms_ import negationElim
        return negationElim.specialize({A:self.operand}, assumptions=assumptions)
    
    def deriveViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot \lnot A`, derive and return :math:`A` assuming :math:`A \in \mathbb{B}`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from _theorems_ import fromDoubleNegation
        if isinstance(self.operand, Not):
            return fromDoubleNegation.specialize({A:self.operand.operand}, aassumptions=assumptions)
        raise ValueError("deriveViaDoubleNegation does not apply to " + str(self) + " which is not of the form Not(Not(A))")

    def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        Prove and return self of the form :math:`\lnot \lnot A` assuming :math:`A`.
        Also see version in NotEquals for :math:`A \neq \bot`.
        '''
        from _theorems_ import doubleNegation
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return doubleNegation.specialize({A:stmt}, assumptions=assumptions)

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
        from _theorems_ import contradictionViaNegation
        return contradictionViaNegation.specialize({A:self.operand}, assumptions=assumptions)
    
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
