from proveit import Literal, Operation, USE_DEFAULTS
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
        if self.operand != FALSE:
            self.equateNegatedToFalse(knownTruth.assumptions)
        self.deriveContradiction(knownTruth.assumptions)
        if isinstance(self.operand, Not):
            self.deriveViaDoubleNegation(knownTruth.assumptions)
        if isinstance(self.operand, Equals):
            self.deriveNotEquals(knownTruth.assumptions)
        if isinstance(self.operand, InSet):
            self.deriveNotIn(knownTruth.assumptions)
        if isinstance(self.operand, Exists):
            self.deriveNotExists(knownTruth.assumptions)
    
    def conclude(self, assumptions):
        '''
        Can automatically conclude Not(Not(A)) from A.
        '''
        if isinstance(self.operand, Not):
            self.concludeViaDoubleNegation(assumptions)
        
    @classmethod
    def operatorOfOperation(subClass):
        return NOT
    
    def latex(self, fence=False):
        outStr = ''
        if fence: outStr += "("
        outStr += self.operator.latex() + ' ' + self.operand.latex(fence=True)
        if fence: outStr += ')'
        return outStr            
    
    def evaluate(self):
        '''
        Given an operand that evaluates to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from proveit.logic import Equals
        from axioms import notT, notF
        if self.operand == TRUE: return notT
        elif self.operand == FALSE: return notF
        def doEval():
            operandEval = self.operand.evaluate()
            if operandEval.rhs == TRUE: 
                val = notT.rhs
            elif operandEval.rhs == FALSE: 
                val = notF.rhs
            return operandEval.lhsSubstitute(Equals(Not(A), val), A)
        return _evaluate(self, doEval)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'not' expression is in the set of BOOLEANS.
        '''
        from theorems import negationClosure
        return negationClosure.specialize({A:self.operand}, assumptions)
   
    def equateNegatedToFalse(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot A`, derive and return :math:`A = \bot`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from theorems import eqFalseFromNot
        return eqFalseFromNot.specialize({A:self.operand}, assumptions)
    
    def deriveViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot \lnot A`, derive and return :math:`A` assuming :math:`A \in \mathbb{B}`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from theorems import fromDoubleNegation
        if isinstance(self.operand, Not):
            return fromDoubleNegation.specialize({A:self.operand.operand}, assumptions)
        raise ValueError("deriveViaDoubleNegation does not apply to " + str(self) + " which is not of the form Not(Not(A))")

    def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        r'''
        Prove and return self of the form :math:`\lnot \lnot A` assuming :math:`A`.
        Also see version in NotEquals for :math:`A \neq \bot`.
        '''
        from theorems import doubleNegation
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return doubleNegation.specialize({A:stmt}, assumptions)
            
    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot A`, derive and return :math:`A \Rightarrow \bot`.
        '''
        from theorems import contradictionFromNegation
        return contradictionFromNegation.specialize({A:self.operand}).deriveConclusion(assumptions)
    
    def deriveNotEquals(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot(A = B)`, derive and return :math:`A \neq B`.
        '''
        from proveit.logic import Equals
        from proveit.logic.equality.theorems import foldNotEquals
        if isinstance(self.operand, Equals):
            return foldNotEquals.specialize({x:self.operand.lhs, y:self.operand.rhs}).deriveConclusion(assumptions)

    def deriveNotIn(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`\lnot(A \in B)`, derive and return :math:`A \notin B`.
        '''
        from proveit.logic import InSet
        from proveit.logic.set_theory.theorems import foldNotIn
        if isinstance(self.operand, InSet):
            return foldNotIn.specialize({x:self.operand.element, S:self.operand.domain}).deriveConclusion(assumptions)

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
        from theorems import doubleNegationEquiv
        if isinstance(self.operand, Not):
            Asub = self.operand.operand
            return doubleNegationEquiv.specialize({A:Asub}, assumptions=assumptions)
