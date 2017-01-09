from proveit import Literal, BinaryOperation, USE_DEFAULTS, compositeExpression, tryDerivation
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from proveit.logic.boolean.negation import Not
from proveit.common import A, B, C

IMPLIES = Literal(__package__, stringFormat = '=>', latexFormat = r'\Rightarrow')

class Implies(BinaryOperation):
    # map Expressions to sets of KnownTruths of implications that involve the Expression
    # as the hypothesis or the conclusion
    knownImplications = dict()    
    
    def __init__(self, hypothesis, conclusion):
        BinaryOperation.__init__(self, IMPLIES, hypothesis, conclusion)
        self.hypothesis = self.lhs = hypothesis
        self.conclusion = self.rhs = conclusion

    @classmethod
    def operatorOfOperation(subClass):
        return IMPLIES    

    def deriveSideEffects(self, knownTruth):
        '''
        Record the KnownTruth implication in the dictionary of knownImplications so we
        can perform a search to later prove other implications via transitivity.
        Also automatically derive the conclusion given the hypothesis as an added assumption.
        From A => FALSE, automatically derive Not(A) if [A in Booleans].
        From Not(A) => FALSE, automatically derive A if [A in Booleans].
        '''
        Implies.knownImplications.setdefault(self.hypothesis, set()).add(knownTruth)
        Implies.knownImplications.setdefault(self.conclusion, set()).add(knownTruth)
        try:
            self.deriveConclusion(knownTruth.assumptions + (self.hypothesis,))
        except:
            pass
        if self.conclusion == FALSE:
            tryDerivation(self.deriveViaContradiction, knownTruth.assumptions)
    
    def conclude(self, assumptions):
        '''
        Try to automatically conclude this implication by reducing its operands
        to true/false, or by doing a "transitivity" search amongst known true implications
        whose assumptions are covered by the given assumptions.
        '''
        from _theorems_ import trueImpliesTrue, falseImpliesTrue, falseImpliesFalse
        from proveit.logic import transitivitySearch        
        if self in {trueImpliesTrue, falseImpliesTrue, falseImpliesFalse}:
            # should be proven via one of the imported theorems as a simple special case
            return self.prove()
        try:
            # try to prove the implication via evaluation reduction.
            # if that is possible, it is a relatively straightforward thing to do.
            return BinaryOperation.conclude(assumptions)
        except:
            pass
        try:
            # try to prove the implication via hypothetical reasoning.
            return self.conclusion.prove(assumptions + (self.hypothesis,)).asImplication(self.hypothesis)
        except:
            pass
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        return transitivitySearch(self, assumptions)

    @staticmethod
    def knownRelationsFromLeft(expr, assumptionsSet):
        '''
        For each KnownTruth that is an Implies involving the given expression on
        the left hand side (the hypothesis), yield the KnownTruth and the right hand side
        (the conclusions).
        '''
        for knownTruth in Implies.knownImplications.get(expr, frozenset()):
            if knownTruth.hypothesis == expr:
                if assumptionsSet.issuperset(knownTruth.assumptions):
                    yield (knownTruth, knownTruth.conclusion)
    
    @staticmethod
    def knownRelationsFromRight(expr, assumptionsSet):
        '''
        For each KnownTruth that is an Equals involving the given expression on
        the right hand side (the conclusion), yield the KnownTruth and the left hand side
        (the hypothesis).
        '''
        for knownTruth in Implies.knownImplications.get(expr, frozenset()):
            if knownTruth.conclusion == expr:
                if assumptionsSet.issuperset(knownTruth.assumptions):
                    yield (knownTruth, knownTruth.hypothesis)
                    
    def deriveConclusion(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \Rightarrow B)` derive and return :math:`B` assuming :math:`A`.
        '''
        from proveit._core_.proof import ModusPonens
        return ModusPonens(self, assumptions).provenTruth
                
    def applyTransitivity(self, otherImpl, assumptions=USE_DEFAULTS):
        '''
        From :math:`A \Rightarrow B` (self) and a given :math:`B \Rightarrow C` (otherImpl), derive and return :math:`A \Rightarrow C`.
        '''
        from _theorems_ import implicationTransitivity
        if self.conclusion == otherImpl.hypothesis:
            return implicationTransitivity.specialize({A:self.hypothesis, B:self.conclusion, C:otherImpl.conclusion}, assumptions=assumptions)
        elif self.hypothesis == otherImpl.conclusion:
            return implicationTransitivity.specialize({A:otherImpl.hypothesis, B:self.hypothesis, C:self.conclusion}, assumptions=assumptions)
    
    def deriveViaContradiction(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`[\lnot A \Rightarrow \bot]`, derive and return :math:`A` assuming :math:`A \in \mathcal{B}`.
        Or from :math:`[A \Rightarrow \bot]`, derive and return :math:`\lnot A` assuming :math:`A \in \mathcal{B}`.
        '''
        from proveit.logic.boolean.negation._axioms_ import contradictoryValidation
        from proveit.logic.boolean.negation._theorems_ import hypotheticalContradiction
        if self.conclusion != FALSE:
            raise ValueError('deriveViaContridiction method is only applicable if FALSE is implicated, not for ' + str(self))
        if isinstance(self.hypothesis, Not):
            stmt = self.hypothesis.operand
            return contradictoryValidation.specialize({A:stmt}, assumptions).deriveConclusion(assumptions)
        else:
            return hypotheticalContradiction.specialize({A:self.hypothesis}, assumptions).deriveConclusion(assumptions)
    
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
        from _theorems_ import transpositionFromNegated, transpositionFromNegatedConclusion, transpositionFromNegatedHypothesis, transpositionToNegated
        from proveit.logic import Not
        if isinstance(self.hypothesis, Not) and isinstance(self.conclusion, Not):
            return transpositionFromNegated.specialize({B:self.hypothesis.operand, A:self.conclusion.operand})
        elif isinstance(self.hypothesis, Not):
            return transpositionFromNegatedHypothesis.specialize({B:self.hypothesis.operand, A:self.conclusion})
        elif isinstance(self.conclusion, Not):
            return transpositionFromNegatedConclusion.specialize({B:self.hypothesis, A:self.conclusion.operand})
        else:
            return transpositionToNegated.specialize({B:self.hypothesis, A:self.conclusion})
        
    def transpose(self, assumptions=USE_DEFAULTS):
        '''
        Depending upon the form of self with respect to negation of the hypothesis and/or conclusion,
        will derive from self and return as follows:
        
        * From :math:`[\lnot A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[\lnot A \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        '''
        return self.transposition().deriveConclusion(assumptions)
        
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from _axioms_ import impliesTF # load in truth-table evaluations
        from _theorems_ import impliesTT, impliesFT, impliesFF
        return BinaryOperation.evaluate(self, assumptions)
    
    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this implication expression is in the set of BOOLEANS.
        '''
        from _theorems_ import implicationClosure
        hypothesisInBool = deduceInBool(self.hypothesis)
        conclusionInBool = deduceInBool(self.conclusion)
        return implicationClosure.specialize({A:self.hypothesis, B:self.conclusion})