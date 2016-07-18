from proveit import Literal, BinaryOperation, USE_DEFAULTS, compositeExpression
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.logic.boolean.negation import Not
from proveit.common import A, B

IMPLIES = Literal(__package__, stringFormat = '=>', latexFormat = r'\Rightarrow')

class Implies(BinaryOperation):
    def __init__(self, hypothesis, conclusion):
        BinaryOperation.__init__(self, IMPLIES, hypothesis, conclusion)
        self.hypothesis = hypothesis
        self.conclusion = conclusion

    @classmethod
    def operatorOfOperation(subClass):
        return IMPLIES    

    def deriveConclusion(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \Rightarrow B)` derive and return :math:`B` assuming :math:`A`.
        '''
        from proveit._core_.proof import ModusPonens
        return ModusPonens(self, assumptions).provenTruth
                
    def applySyllogism(self, otherImpl, assumptions=USE_DEFAULTS):
        '''
        From :math:`A \Rightarrow B` (self) and a given :math:`B \Rightarrow C` (otherImpl), derive and return :math:`A \Rightarrow C`.
        '''
        assert isinstance(otherImpl, Implies), "expected an Implies object"
        if self.conclusion == otherImpl.hypothesis:
            return Implies(self.hypothesis, otherImpl.conclusion).proven(assumptions)
        elif self.hypothesis == otherImpl.conclusion:
            return Implies(otherImpl.hypothesis, self.conclusion).proven(assumptions)
    
    def deriveViaContradiction(self):
        r'''
        From :math:`[\lnot A \Rightarrow \mathtt{FALSE}]`, derive and return :math:`A` assuming :math:`A \in \mathcal{B}`.
        Or from :math:`[A \Rightarrow \mathtt{FALSE}]`, derive and return :math:`\lnot A` assuming :math:`A \in \mathcal{B}`.
        '''
        from proveit.logic.boolean.negation.axioms import contradictoryValidation
        from proveit.logic.boolean.negation.theorems import hypotheticalContradiction
        assert self.conclusion == FALSE
        if isinstance(self.hypothesis, Not):
            stmt = self.hypothesis.operand
            return contradictoryValidation.specialize({A:stmt}).deriveConclusion()
        else:
            return hypotheticalContradiction.specialize({A:self.hypothesis}).deriveConclusion()
    
    def generalize(self, forallVars, domain=None, conditions=tuple()):
        r'''
        This makes a generalization of this expression, prepending Forall 
        operations according to newForallVars and newConditions and/or newDomain
        that will bind 'arbitrary' free variables.  This overrides the expr 
        version to absorb hypothesis into conditions if they match.  For example, 
        :math:`[A(x) \Rightarrow [B(x, y) \Rightarrow P(x, y)]]` generalized 
        forall :math:`x, y` such that :math:`A(x), B(x, y)`
        becomes :math:`\forall_{x, y | A(x), B(x, y)} P(x, y)`,
        '''
        from proveit.logic import InSet
        hypothesizedConditions = set()
        conditionsSet = set(compositeExpression(conditions))
        if domain is not None:
            # add in the effective conditions from the domain
            for var in compositeExpression(forallVars):
                conditionsSet.add(InSet(var, domain))
        expr = self
        while isinstance(expr, Implies) and expr.hypothesis in conditionsSet:
            hypothesizedConditions.add(expr.hypothesis)
            expr = expr.conclusion
        if len(hypothesizedConditions) == 0:
            # Just use the expr version
            return expr.generalize(self, forallVars, domain, conditions)
        return expr.generalize(expr, forallVars, domain, conditions)
        #return Forall(newForallVars, expr, newConditions)

    def transposition(self):
        r'''
        Depending upon the form of self with respect to negation of the hypothesis and/or conclusion,
        will prove and return as follows:
        
        * For :math:`[\lnot A  \Rightarrow \lnot B]`, prove :math:`[\lnot A \Rightarrow \lnot B] \Rightarrow [B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`.
        * For :math:`[\lnot A \Rightarrow B]`, prove :math:`[\lnot A \Rightarrow B] \Rightarrow [\lnot B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        * For :math:`[A  \Rightarrow \lnot B]`, prove :math:`[A \Rightarrow \lnot B] \Rightarrow [B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`.
        * For :math:`[A  \Rightarrow B]`, prove :math:`[A \Rightarrow B] \Rightarrow [\lnot B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        '''
        from theorems import transpositionFromNegated, transpositionFromNegatedConclusion, transpositionFromNegatedHypothesis, transpositionToNegated
        from proveit.logic import Not
        if isinstance(self.hypothesis, Not) and isinstance(self.conclusion, Not):
            return transpositionFromNegated.specialize({B:self.hypothesis.operand, A:self.conclusion.operand})
        elif isinstance(self.hypothesis, Not):
            return transpositionFromNegatedHypothesis.specialize({B:self.hypothesis.operand, A:self.conclusion})
        elif isinstance(self.conclusion, Not):
            return transpositionFromNegatedConclusion.specialize({B:self.hypothesis, A:self.conclusion.operand})
        else:
            return transpositionToNegated.specialize({B:self.hypothesis, A:self.conclusion})
        
    def transpose(self):
        '''
        Depending upon the form of self with respect to negation of the hypothesis and/or conclusion,
        will derive from self and return as follows:
        
        * From :math:`[\lnot A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[\lnot A \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        '''
        return self.transposition().deriveConclusion()
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from axioms import impliesTF
        from theorems import impliesTT, impliesFT, impliesFF
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return impliesTT
            elif A == TRUE and B == FALSE: return impliesTF
            elif A == FALSE and B == TRUE: return impliesFT
            elif A == FALSE and B == FALSE: return impliesFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))
    
    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this implication expression is in the set of BOOLEANS.
        '''
        from theorems import implicationClosure
        hypothesisInBool = deduceInBool(self.hypothesis)
        conclusionInBool = deduceInBool(self.conclusion)
        return implicationClosure.specialize({A:self.hypothesis, B:self.conclusion})