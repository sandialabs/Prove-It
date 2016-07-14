from proveit import USE_DEFAULTS, Operation, Literal, ExpressionList, compositeExpression
from proveit import BinaryOperation, AssociativeOperation
from boolSet import TRUE, FALSE, deduceInBool
from quantifiers import Exists, NotExists
from proveit.common import A, B, C, x, y, f, a, b, c, S, xEtc, zEtc

pkg = __package__

IMPLIES = Literal(pkg, stringFormat = '=>', latexFormat = r'\Rightarrow')
NOT = Literal(pkg, stringFormat = 'not', latexFormat = r'\lnot')
AND = Literal(pkg, stringFormat = 'and', latexFormat = r'\land')
OR = Literal(pkg, stringFormat = 'or', latexFormat = r'\lor')
IFF = Literal(pkg, stringFormat = '<=>', latexFormat = r'\Leftrightarrow')

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
        from axioms import contradictoryValidation
        from theorems import hypotheticalContradiction
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
        from proveit.logic.set.theorems import foldNotIn
        if isinstance(self.operand, InSet):
            return foldNotIn.specialize({x:self.operand.element, S:self.operand.domain}).deriveConclusion()

    def deriveNotExists(self):
        r'''
        From :math:`\lnot \exists_{x | Q(x)} P(x)`, derive and return :math:`\nexists_{x | Q(x)} P(x)`
        '''
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

class And(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        AssociativeOperation.__init__(self, AND, *operands)
        
    @classmethod
    def operatorOfOperation(subClass):
        return AND
    
    def deriveInPart(self, indexOrExpr):
        r'''
        From :math:`(A \land ... \land X \land ... \land Z)` derive :math:`X`.  indexOrExpr specifies 
        :math:`X` either by index or the expr.
        '''
        from axioms import andImpliesEach
        from proveit.common import Aetc, Cetc
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operands).index(indexOrExpr)
        return andImpliesEach.specialize({Aetc:self.operands[:idx], B:self.operands[idx], Cetc:self.operands[idx+1:]}).deriveConclusion()
        
    def deriveLeft(self):
        '''
        From (A and B), derive and return A.
        '''
        assert len(self.operands) == 2
        return self.deriveInPart(0)

    def deriveRight(self):
        '''
        From (A and B), derive and return B.
        '''
        assert len(self.operands) == 2
        return self.deriveInPart(1)
        
    def decompose(self):
        '''
        From (A and B), derive and return A, B as a tuple.
        '''        
        return (self.deriveLeft(), self.deriveRight())

    def concludeViaComposition(self):
        '''
        Prove and return some (A and B) assuming A, B.  See also the compose method to
        do this constructively.
        '''
        return compose(*self.operands)
            
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from axioms import andComposition, andTT, andTF, andFT, andFF
        if len(self.operands) >= 3:
            # A and B and ..C.. = A and (B and ..C..)
            compositionEquiv = andComposition.specialize({A:self.operands[0], B:self.operands[1], C:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return andTT
            elif A == TRUE and B == FALSE: return andTF
            elif A == FALSE and B == TRUE: return andFT
            elif A == FALSE and B == FALSE: return andFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'and' expression is in the set of BOOLEANS.
        '''
        from theorems import conjunctionClosure
        if len(self.operands) > 2:
            raise Exception('Deducing more than binary conjunction in booleans has not been implemented')
        inBools = {deduceInBool(operand) for operand in self.operands}
        return conjunctionClosure.specialize({A:self.operands[0], B:self.operands[1]})

class Or(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Or together any number of operands: A or B or C
        '''
        AssociativeOperation.__init__(self, OR, *operands)

    @classmethod
    def operatorOfOperation(subClass):
        return OR
    
    def deriveRightIfNotLeft(self):
        '''
        From (A or B) derive and return B assuming Not(A), inBool(B). 
        '''
        from theorems import orImpliesRightIfNotLeft
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return orImpliesRightIfNotLeft.specialize({A:leftOperand, B:rightOperand}).deriveConclusion()

    def deriveLeftIfNotRight(self):
        '''
        From (A or B) derive and return A assuming inBool(A), Not(B).
        '''
        from theorems import orImpliesLeftIfNotRight
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return orImpliesLeftIfNotRight.specialize({A:leftOperand, B:rightOperand}).deriveConclusion()
        
    def deriveCommonConclusion(self, conclusion):
        '''
        From (A or B) derive and return the provided conclusion C assuming A=>C, B=>C, A,B,C in BOOLEANS.
        '''
        from theorems import hypotheticalDisjunction
        # forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        leftImplConclusion = Implies(leftOperand, conclusion)
        rightImplConclusion = Implies(rightOperand, conclusion)
        # (A=>C and B=>C) assuming A=>C, B=>C
        compose(leftImplConclusion, rightImplConclusion)
        return hypotheticalDisjunction.specialize({A:leftOperand, B:rightOperand, C:conclusion}).deriveConclusion().deriveConclusion()
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from axioms import orComposition, orTT, orTF, orFT, orFF
        if len(self.operands) >= 3:
            # A or B or ..C.. = A or (B or ..C..)
            compositionEquiv = orComposition.specialize({A:self.operands[0], B:self.operands[1], C:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return orTT
            elif A == TRUE and B == FALSE: return orTF
            elif A == FALSE and B == TRUE: return orFT
            elif A == FALSE and B == FALSE: return orFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'or' expression is in the set of BOOLEANS.
        '''
        from theorems import disjunctionClosure
        leftInBool = deduceInBool(self.leftOperand)
        rightInBool = deduceInBool(self.rightOperand)
        return disjunctionClosure.specialize({A:self.hypothesis, B:self.conclusion})
    
    def concludeViaExample(self, trueOperand):
        '''
        From one true operand, conclude that this 'or' expression is true.
        Requires all of the operands to be in the set of BOOLEANS.
        '''
        from theorems import orIfAny
        index = self.operands.index(trueOperand)
        return orIfAny.specialize({xEtc:self.operands[:index], y:self.operands[index], zEtc:self.operands[index+1:]})

# if and only if: A => B and B => A
class Iff(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, IFF, A, B)
        self.A = A
        self.B = B

    @classmethod
    def operatorOfOperation(subClass):
        return IFF
        
    def deriveLeftImplication(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return B=>A.
        '''
        from theorems import iffImpliesLeft
        return iffImpliesLeft.specialize({A: self.A, B: self.B}).deriveConclusion(assumptions)
        
    def deriveLeft(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return A assuming B.
        '''
        return self.deriveLeftImplication(assumptions).deriveConclusion(assumptions)

    def deriveRightImplication(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return A=>B.
        '''
        from theorems import iffImpliesRight
        return iffImpliesRight.specialize({A: self.A, B: self.B}).deriveConclusion(assumptions)

    def deriveRight(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return B assuming A.
        '''
        return self.deriveRightImplication().deriveConclusion(assumptions)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From (A<=>B) derive and return (B<=>A).
        '''
        from theorems import iffSymmetry
        return iffSymmetry.specialize({A:self.A, B:self.B}).deriveConclusion(assumptions)
    
    def applyTransitivity(self, otherIff, assumptions=USE_DEFAULTS):
        '''
        From A <=> B (self) and the given B <=> C (otherIff) derive and return 
        (A <=> C) assuming self and otherIff.
        Also works more generally as long as there is a common side to the equations.
        '''
        from theorems import iffTransitivity
        assert isinstance(otherIff, Iff)
        if self.B == otherIff.A:
            # from A <=> B, B <=> C, derive A <=> C
            compose(self, otherIff) # A <=> B and B <=> C
            return iffTransitivity.specialize({A:self.A, B:self.B, C:otherIff.B}).deriveConclusion(assumptions)
        elif self.A == otherIff.A:
            # from y = x and y = z, derive x = z
            return self.deriveReversed(assumptions).applyTransitivity(otherIff, assumptions)
        elif self.A == otherIff.B:
            # from y = x and z = y, derive x = z
            return self.deriveReversed(assumptions).applyTransitivity(otherIff.deriveReversed(assumptions))
        elif self.B == otherIff.B:
            # from x = y and z = y, derive x = z
            return self.applyTransitivity(otherIff.deriveReversed(assumptions))
        else:
            assert False, 'transitivity cannot be applied unless there is something in common in the equalities'
        
    def definition(self):
        '''
        Return (A <=> B) = [(A => B) and (B => A)] where self represents (A <=> B).
        '''
        from axioms import iffDef
        return iffDef.specialize({A:self.A, B:self.B})
    
    def concludeViaComposition(self, assumptions=USE_DEFAULTS):
        '''
        Conclude (A <=> B) assuming both (A => B), (B => A).
        '''
        AimplB = Implies(self.A, self.B) 
        BimplA = Implies(self.B, self.A) 
        compose(AimplB, BimplA)
        return self.definition().deriveLeftViaEquivalence(assumptions)
    
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from theorems import iffTT, iffTF, iffFT, iffFF
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return iffTT
            elif A == TRUE and B == FALSE: return iffTF
            elif A == FALSE and B == TRUE: return iffFT
            elif A == FALSE and B == FALSE: return iffFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'iff' expression is in the set of BOOLEANS.
        '''
        from theorems import iffClosure
        leftInBool = deduceInBool(self.A, assumptions)
        rightInBool = deduceInBool(self.B, assumptions)
        return iffClosure.specialize({A:self.hypothesis, B:self.conclusion})
    
    def deriveEquality(self, assumptions=USE_DEFAULTS):
        '''
        From (A <=> B), derive (A = B) assuming A and B in BOOLEANS.
        '''
        from theorems import iffOverBoolImplEq
        return iffOverBoolImplEq.specialize({A:self.A, B:self.B}).deriveConclusion(assumptions)

def deriveStmtEqTrue(statement):
    '''
    For a given statement, derive statement = TRUE assuming statement.
    '''
    from proveit.logic import Equals
    return Equals(statement, TRUE).concludeBooleanEquality()

def compose(*expressions):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    from axioms import andComposition
    from theorems import conjunctionIntro
    if len(expressions) == 2:
        exprA, exprB = expressions
        return conjunctionIntro.specialize({A:exprA, B:exprB})
    else:
        assert len(expressions) > 2, "Compose 2 or more expressions, but not less than 2."
        rightComposition = compose(*expressions[1:])
        # A and (B and ..C..) = TRUE, given A, B, ..C..
        nestedAndEqT = deriveStmtEqTrue(compose(expressions[0], rightComposition))
        # A and B and ..C.. = A and (B and ..C..)
        compositionEquality = andComposition.specialize({A:expressions[0], B:rightComposition.operands[0], C:rightComposition.operands[1:]})
        print nestedAndEqT
        print compositionEquality
        # [A and B and ..C..] given A, B, ..C..
        return compositionEquality.applyTransitivity(nestedAndEqT).deriveViaBooleanEquality()

def _evaluateBooleanBinaryOperation(operation, baseEvalFn):
    from proveit.logic.equality.theorems import unaryEvaluation, binaryEvaluation
    _x = operation.operands[0]
    _y = operation.operands[1]
    operator = operation.operator
    if (_x == TRUE or _x == FALSE) and (_y == TRUE or _y == FALSE):
        evaluation = baseEvalFn(_x, _y)
    elif (_x == TRUE or _x == FALSE):
        _b = _y.evaluate().rhs
        _c = baseEvalFn(_x, _b).rhs
        dummyVar = _x.safeDummyVar() # var that isn't in _x
        fOp = operation(f, dummyVar)
        fOpSub =  operation.make(operator, ExpressionList(_x, dummyVar))
        evaluation = unaryEvaluation.specialize({fOp:fOpSub, x:_y, a:_b, c:_c}).deriveConclusion().deriveConclusion()
    elif (_y == TRUE or _y == FALSE):
        _a = _x.evaluate().rhs
        _c = baseEvalFn(_a, _y).rhs
        dummyVar = _y.safeDummyVar() # var that isn't in _y
        fOp = operation(f, dummyVar)
        fOpSub = operation.make(operator, ExpressionList(dummyVar, _y))
        evaluation = unaryEvaluation.specialize({fOp:fOpSub, x:_x, a:_a, c:_c}).deriveConclusion().deriveConclusion()
    else:
        xEval = _x.evaluate()
        yEval = _y.evaluate()
        compose(xEval, yEval)
        _a, _b = xEval.rhs, yEval.rhs 
        _c = baseEvalFn(_a, _b).rhs
        fOp = operation(f, (a, b))
        fOpSub = operation.make(operator, ExpressionList(a, b))
        # f(_x, _y) = _c
        evaluation = binaryEvaluation.specialize({fOp:fOpSub, x:_x, y:_y, a:_a, b:_b, c:_c}).deriveConclusion().deriveConclusion()
    return evaluation    

"""
def _evaluate(expr, evalFn):
    '''
    Lookup or perform (via evalFn) and store an evaluation of the given boolean expression.
    '''
    if expr in self.evalLookup:
        return self.eval[self.evalLookup[expr]]
    else:
        evaluation = evalFn()
        if evaluation != None:
            self.evalLookup[expr] = len(self.eval)
            self.eval.append(evaluation)
            if evaluation.qed().statement.getRegisteredVar() == None:
                booleans.register('eval', len(booleans.eval)-1)            
        return evaluation
"""

def _evaluate(expr, evalFn):
    '''
    Simple version for now.  The future plan is to store/unnamed unnamed theorems -- anything
    proven that has no free variables or assumptions.
    '''
    return evalFn()

