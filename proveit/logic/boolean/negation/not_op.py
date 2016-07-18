from proveit import Literal, Operation
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.common import A, x, y, S

NOT = Literal(__package__, stringFormat = 'not', latexFormat = r'\lnot')

class Not(Operation):
    def __init__(self, A):
        Operation.__init__(self, NOT, A)
        self.operand = A

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

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'not' expression is in the set of BOOLEANS.
        '''
        from theorems import negationClosure
        operandInBool = deduceInBool(self.operand)
        return negationClosure.specialize({A:self.operand})
   
    def equateNegatedToFalse(self):
        r'''
        From :math:`\lnot A`, derive and return :math:`A = \mathtt{FALSE}`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from theorems import notImpliesEqFalse
        return notImpliesEqFalse.specialize({A:self.operand}).deriveConclusion()

    def equateFalseToNegated(self):
        r'''
        From :math:`\lnot A`, derive and return :math:`\mathtt{FALSE} = A`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from theorems import notImpliesEqFalseRev
        return notImpliesEqFalseRev.specialize({A:self.operand}).deriveConclusion()
    
    def deriveViaDoubleNegation(self):
        r'''
        From :math:`\lnot \lnot A`, derive and return :math:`A` assuming :math:`A \in \mathcal{B}`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        from theorems import fromDoubleNegation
        if isinstance(self.operand, Not):
            return fromDoubleNegation.specialize({A:self.operand.operand}).deriveConclusion()

    def concludeViaDoubleNegation(self):
        r'''
        Prove and return self of the form :math:`\lnot \lnot A` assuming :math:`A`.
        Also see version in NotEquals for :math:`A \neq \mathtt{FALSE}`.
        '''
        from theorems import doubleNegation
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return doubleNegation.specialize({A:stmt}).deriveConclusion()
            
    def deriveContradiction(self):
        r'''
        From :math:`\lnot A`, derive and return :math:`A \Rightarrow \mathtt{FALSE}`.
        '''
        from theorems import contradictionFromNegation
        return contradictionFromNegation.specialize({A:self.operand}).deriveConclusion()
    
    def deriveNotEquals(self):
        r'''
        From :math:`\lnot(A = B)`, derive and return :math:`A \neq B`.
        '''
        from proveit.logic import Equals
        from proveit.logic.equality.theorems import foldNotEquals
        if isinstance(self.operand, Equals):
            return foldNotEquals.specialize({x:self.operand.lhs, y:self.operand.rhs}).deriveConclusion()

    def deriveNotIn(self):
        r'''
        From :math:`\lnot(A \in B)`, derive and return :math:`A \notin B`.
        '''
        from proveit.logic import InSet
        from proveit.logic.set_theory.theorems import foldNotIn
        if isinstance(self.operand, InSet):
            return foldNotIn.specialize({x:self.operand.element, S:self.operand.domain}).deriveConclusion()

    def deriveNotExists(self):
        r'''
        From :math:`\lnot \exists_{x | Q(x)} P(x)`, derive and return :math:`\nexists_{x | Q(x)} P(x)`
        '''
        from proveit.logic import Exists, NotExists
        operand = self.operand
        if isinstance(operand, Exists):
            existsExpr = operand
            notExistsExpr = NotExists(existsExpr.instanceVars, existsExpr.instanceExpr, domain=existsExpr.domain, conditions=existsExpr.conditions)
            return notExistsExpr.concludeAsFolded()
        
    def deduceDoubleNegationEquiv(self):
        '''
        For some Not(Not(A)), derive and return A = Not(Not(A)) assuming A in BOOLEANS.
        '''
        from theorems import doubleNegationEquiv
        if isinstance(self.operand, Not):
            Asub = self.operand.operand
            return doubleNegationEquiv.specialize({A:Asub})
