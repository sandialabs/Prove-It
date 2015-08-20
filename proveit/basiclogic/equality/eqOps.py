from proveit.basiclogic.genericOps import BinaryOperation
from proveit.expression import Variable, Literal, Operation, STRING, LATEX,\
    safeDummyVar
from proveit.common import A, P, X, f, x, y, z

pkg = __package__

class Equals(BinaryOperation):
    def __init__(self, a, b):
        BinaryOperation.__init__(self, EQUALS, a, b)
        self.lhs = a
        self.rhs = b

    def concludeViaReflexivity(self):
        '''
        Prove and return self of the form x = x.
        '''
        from axioms import equalsReflexivity
        assert self.lhs == self.rhs
        return equalsReflexivity.specialize({x:self.lhs}).checked()
            
    def deriveReversed(self):
        '''
        From x = y derive y = x.
        '''
        from axioms import equalsSymmetry
        return equalsSymmetry.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})

    def transitivityImpl(self, otherEquality):
        '''
        From x = y (self) and the given y = z (otherEquality) derive and return 
        (y=z) => (x = z) assuming self.
        Also works more generally as long as there is a common side to the equations.
        '''
        from axioms import equalsTransitivity
        assert isinstance(otherEquality, Equals)
        if self.rhs == otherEquality.lhs:
            # from x = y, y = z, derive y = z => x = z assuing x = y
            result = equalsTransitivity.specialize({x:self.lhs, y:self.rhs, z:otherEquality.rhs}).deriveConclusion()
            return result.checked({self})
        elif self.lhs == otherEquality.lhs:
            # from y = x and y = z, derive y = z => x = z assuing x = y
            return self.deriveReversed().transitivityImpl(otherEquality)
        elif self.lhs == otherEquality.rhs:
            # from y = x and z = y, derive y = z => x = z assuing x = y
            return self.deriveReversed().transitivityImpl(otherEquality.deriveReversed())
        elif self.rhs == otherEquality.rhs:
            # from x = y and z = y, derive y = z => x = z assuing x = y
            return self.transitivityImpl(otherEquality.deriveReversed())
        else:
            assert False, 'transitivity cannot be applied unless there is something in common in the equalities'
            
    def applyTransitivity(self, otherEquality):
        '''
        From x = y (self) and y = z (otherEquality) derive and return x = z.
        Also works more generally as long as there is a common side to the equations.
        '''
        return self.transitivityImpl(otherEquality).deriveConclusion().checked({self, otherEquality})
        
    def deriveViaBooleanEquality(self):
        '''
        From A = TRUE or TRUE = A derive A, or from A = FALSE or FALSE = A derive Not(A).
        Note, see deriveStmtEqTrue or Not.equateNegatedToFalse for the reverse process.
        '''
        from proveit.basiclogic import TRUE, FALSE        
        from proveit.basiclogic.boolean.axioms import eqTrueElim
        from proveit.basiclogic.boolean.theorems import eqTrueRevElim, notFromEqFalse, notFromEqFalseRev
        if self.lhs == TRUE:
            return eqTrueRevElim.specialize({A:self.rhs}).deriveConclusion().checked({self}) # A
        elif self.rhs == TRUE:
            return eqTrueElim.specialize({A:self.lhs}).deriveConclusion().checked({self}) # A
        elif self.lhs == FALSE:
            return notFromEqFalseRev.specialize({A:self.rhs}).deriveConclusion().checked({self}) # Not(A)            
        elif self.rhs == FALSE:
            return notFromEqFalse.specialize({A:self.lhs}).deriveConclusion().checked({self}) # Not(A)
        
    def deriveContradiction(self):
        '''
        From A=FALSE, derive A=>FALSE.
        '''
        from proveit.basiclogic import FALSE        
        from theorems import contradictionFromFalseEquivalence, contradictionFromFalseEquivalenceReversed
        if self.rhs == FALSE:
            return contradictionFromFalseEquivalence.specialize({A:self.lhs}).deriveConclusion().checked({self})
        elif self.lhs == FALSE:
            return contradictionFromFalseEquivalenceReversed.specialize({A:self.rhs}).deriveConclusion().checked({self})
    
    def concludeBooleanEquality(self):
        '''
        Prove and return self of the form (A=TRUE) assuming A, (TRUE=A) assuming A, 
        A=FALSE assuming Not(A), FALSE=A assuming Not(A), [Not(A)=FALSE] assuming A, or [FALSE=Not(A)] assuming A.
        '''
        from proveit.basiclogic import TRUE, FALSE, Not        
        from proveit.basiclogic.boolean.axioms import eqTrueIntro
        from proveit.basiclogic.boolean.theorems import eqTrueRevIntro, eqFalseFromNegation, eqFalseRevFromNegation
        if self.rhs == TRUE:
            return eqTrueIntro.specialize({A:self.lhs}).deriveConclusion().checked({self.lhs})
        elif self.rhs == FALSE:
            if isinstance(self.lhs, Not):
                return eqFalseFromNegation.specialize({A:self.lhs.operands}).deriveConclusion().checked({self.lhs.operands})
            else:
                return Not(self.lhs).equateNegatedToFalse()
        elif self.lhs == TRUE:
            return eqTrueRevIntro.specialize({A:self.rhs}).deriveConclusion().checked({self.rhs})
        elif self.lhs == FALSE:
            if isinstance(self.rhs, Not):
                return eqFalseRevFromNegation.specialize({A:self.rhs.operands}).deriveConclusion().checked({self.rhs.operands})
            else:
                return Not(self.rhs).equateFalseToNegated()
    
    def deriveIsInSingleton(self):
        '''
        From (x = y), derive (x in {y}).
        '''
        from proveit.basiclogic.set.axioms import singletonDef
        singletonDef.specialize({x:self.lhs, y:self.rhs}).deriveLeft().checked({self})
    
    def substitution(self, fnArg=None, fnExpr=None):
        '''
        From x = y, and given a function f(x), derive f(x)=f(y).  f(x) is defined by the
        fnArg argument and fnExpr expression.  If fnArg is None then all occurences
        of self.lhs in fnExpr will be substituted with self.rhs.
        '''
        from axioms import substitution
        if fnArg is None:
            # find all occurences of self.lhs within fnExpr to replace with self.rhs
            fnArg = safeDummyVar(self, fnExpr)
            fnExpr = fnExpr.substituted({self.lhs:fnArg})
        assert isinstance(fnArg, Variable)
        return substitution.specialize({x:self.lhs, y:self.rhs, Operation(f, fnArg):fnExpr}).deriveConclusion().checked({self})
        
    def lhsStatementSubstitution(self, fnArg, fnExpr):
        '''
        From x = y, and given a lambda function P(x), derive P(y)=>P(x).  P(x) is defined by the fnArg argument
        and fnExpr expression.
        '''
        from theorems import lhsSubstitution
        assert isinstance(fnArg, Variable)
        return lhsSubstitution.specialize({x:self.lhs, y:self.rhs, Operation(P, fnArg):fnExpr}).deriveConclusion().checked({self})
    
    def rhsStatementSubstitution(self, fnArg, fnExpr):
        '''
        From x = y, and given a lambda function P(x), derive P(x)=>P(y).  P(x) is defined by the fnArg argument
        and fnExpr expression.
        '''
        from theorems import rhsSubstitution
        assert isinstance(fnArg, Variable)
        return rhsSubstitution.specialize({x:self.lhs, y:self.rhs, Operation(P, fnArg):fnExpr}).deriveConclusion().checked({self})

    def lhsSubstitute(self, fnArg, fnExpr):
        '''
        From x = y, and given a lambda function P(x), derive P(x) assuming P(y)
        '''
        substitution = self.lhsStatementSubstitution(fnArg, fnExpr)
        return substitution.deriveConclusion().checked({self, substitution.hypothesis})
        
    def rhsSubstitute(self, fnArg, fnExpr):
        '''
        From x = y, and given a lambda function P(x), derive P(y) assuming P(x)
        '''
        substitution = self.rhsStatementSubstitution(fnArg, fnExpr)
        return substitution.deriveConclusion().checked({self, substitution.hypothesis})

    def leftImplViaEquivalence(self):
        '''
        From A = B, derive B=>A
        '''
        return self.lhsStatementSubstitution(X, X).checked({self})

    def rightImplViaEquivalence(self):
        '''
        From A = B, derive A=>B
        '''
        return self.rhsStatementSubstitution(X, X).checked({self})
        
    def deriveRightViaEquivalence(self):
        '''
        From A = B, derive B (the Right-Hand-Side) assuming A.
        '''
        return self.rhsSubstitute(X, X).checked({self, self.lhs})

    def deriveLeftViaEquivalence(self):
        '''
        From A = B, derive A (the Right-Hand-Side) assuming B.
        '''
        return self.lhsSubstitute(X, X).checked({self, self.rhs})
    
    def deduceInBool(self):
        '''
        Deduce and return that this equality statement is in the set of BOOLEANS.
        '''
        from axioms import equalityInBool
        return equalityInBool.specialize({x:self.lhs, y:self.rhs}).checked()
    
    def inBoolViaBooleanEquality(self):
        '''
        From A=TRUE, A=FALSE, TRUE=A, or FALSE=A, derive and return inBool(A).
        '''
        from proveit.basiclogic import TRUE, FALSE
        from proveit.basiclogic.boolean.theorems import inBoolIfEqTrue, inBoolIfEqTrueRev, inBoolIfEqFalse, inBoolIfEqFalseRev
        if self.rhs == TRUE:
            return inBoolIfEqTrue.specialize({A:self.lhs}).deriveConclusion().proven({self})
        if self.lhs == TRUE:
            return inBoolIfEqTrueRev.specialize({A:self.rhs}).deriveConclusion().proven({self})
        if self.rhs == FALSE:
            return inBoolIfEqFalse.specialize({A:self.lhs}).deriveConclusion().proven({self})
        if self.lhs == FALSE:
            return inBoolIfEqFalseRev.specialize({A:self.rhs}).deriveConclusion().proven({self})
    
    def evaluate(self):
        '''
        Given operands that may be evaluated, derive and return this
        expression equated to TRUE or FALSE.  If both sides equate to
        the same, it will equate to TRUE.  Otherwise, it calls
        evalEquality using the evaluated left and right hand sides
        of the expression to determine the evaluation of the equality.
        '''
        from proveit.basiclogic import TRUE
        from proveit.basiclogic.boolean.boolOps import _evaluate
        def doEval():
            '''
            Performs the actual work if we can't simply look up the evaluation.
            '''
            if self.lhs == self.rhs:
                # simple case where both sides are the same, use reflexivity
                return Equals(self.concludeViaReflexivity(), TRUE).concludeBooleanEquality()
            
            # evaluate both sides and see if simplification is possible
            lhsSimpl = self.lhs
            rhsSimpl = self.rhs
            try:
                lhsEval = self.lhs.evaluate()
                lhsSimpl = lhsEval.rhs
            except AttributeError:
                lhsEval = None
            try:
                rhsEval = self.rhs.evaluate()
                rhsSimpl = rhsEval.rhs
            except AttributeError:
                rhsEval = None
    
            if lhsEval is None and rhsEval is None:
                # Cannot simplify further.  Use evalEquality.
                return lhsSimpl.evalEquality(rhsSimpl)
            else:         
                # evaluate the simplified version
                simplEval = Equals(lhsSimpl, rhsSimpl).evaluate()
                val = simplEval.rhs
                # Using substitution, go from simplEval to self=val
                if lhsEval is not None:
                    lhsEval.lhsSubstitute(X, Equals(Equals(X, rhsSimpl), val))
                if rhsEval is not None:
                    rhsEval.lhsSubstitute(X, Equals(Equals(self.lhs, X), val))
                return Equals(self, val)
            
        return _evaluate(self, doEval)

EQUALS = Literal(pkg, 'EQUALS', {STRING:'=', LATEX:'='}, lambda operands : Equals(*operands))
        
class NotEquals(BinaryOperation):
    def __init__(self, a, b):
        BinaryOperation.__init__(self, NOTEQUALS, a, b)
        self.lhs = a
        self.rhs = b
        
    def deriveReversed(self):
        '''
        From x != y derive y != x.
        '''
        from theorems import notEqualsSymmetry
        return notEqualsSymmetry.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})

    def deriveViaDoubleNegation(self):
        '''
        From A != FALSE, derive and return A assuming inBool(A).
        Also see version in Not class.
        '''
        from proveit.basiclogic import FALSE, inBool
        from proveit.basiclogic.boolean.theorems import fromNotFalse
        if self.rhs == FALSE:
            return fromNotFalse.specialize({A:self.lhs}).deriveConclusion().checked({self, inBool(self.lhs)})

    def concludeViaDoubleNegation(self):
        '''
        Prove and return self of the form A != FALSE assuming A.
        Also see version in Not class.
        '''
        from proveit.basiclogic import FALSE
        from proveit.basiclogic.boolean.theorems import notEqualsFalse
        if self.rhs == FALSE:
            return notEqualsFalse.specialize({A:self.lhs}).deriveConclusion().checked({self.lhs})

    def definition(self):
        '''
        Return (x != y) = Not(x=y) where self represents (x != y).
        '''
        from axioms import notEqualsDef
        return notEqualsDef.specialize({x:self.lhs, y:self.rhs}).checked()

    def unfold(self):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        from theorems import unfoldNotEquals
        return unfoldNotEquals.specialize({x:self.lhs, y:self.rhs}).deriveConclusion().checked({self})

    def evaluate(self):
        '''
        Given operands that may be evaluated, derive and return this
        expression equated to TRUE or FALSE.  If both sides equate to
        the same, it will equate to FALSE.  Otherwise, it calls
        evalEquality using the evaluated left and right hand sides
        of the expression to determine the evaluation of the equality.
        '''
        from proveit.basiclogic.boolean.boolOps import _evaluate
        def doEval():
            '''
            Performs the actual work if we can't simply look up the evaluation.
            '''
            unfoldedEvaluation = self.unfold().evaluate()
            return self.definition().lhsSubstitute(X, Equals(X, unfoldedEvaluation.rhs))
        return _evaluate(self, doEval)    

    def deduceInBool(self):
        '''
        Deduce and return that this 'not equals' statement is in the set of BOOLEANS.
        '''
        from theorems import notEqualsInBool
        return notEqualsInBool.specialize({x:self.lhs, y:self.rhs}).checked()

NOTEQUALS = Literal(pkg, 'NOTEQUALS', {STRING:'!=', LATEX:r'\neq'}, lambda operands : NotEquals(*operands))

