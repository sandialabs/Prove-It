from proveit.expression import Operation, Literal, STRING, LATEX
from proveit.basiclogic.variables import A, P

class BooleanSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'BOOLEANS', {LATEX:r'\cal{B}'})

    def unfoldElemInSet(self, element):
        '''
        From inBool(Element), derive and return [(element = TRUE) or (element = FALSE)].
        '''
        from theorems import unfoldInBool
        #  [(element = TRUE) or (element = FALSE)] assuming inBool(element)
        return unfoldInBool.specialize({A:element}).deriveConclusion().check({inBool(element)})
    
    def deduceElemInSet(self, element):
        '''
        From [(element = TRUE) or (element = FALSE)], derive and return [element in BOOLEANS].
        '''   
        from proveit.basiclogic import Or, Equals
        from theorems import foldInBool
        # prerequisite = [(element = TRUE) or (element = FALSE)]
        prerequisite = Or(Equals(element, TRUE), Equals(element, FALSE))
        # [element in BOOLEANS] assuming prerequisite
        return foldInBool.specialize({A:element}).deriveConclusion().check({prerequisite})

    def evaluateForallInSet(self, forallStmt):
        '''
        Given a forall statement over the set of Booleans, evaluate to TRUE or FALSE
        if possible.
        '''        
        from proveit.basiclogic import Forall, Equals, In
        from theorems import falseEqFalse, trueEqTrue, forallBoolEvalTrue, forallBoolEvalFalseViaTF, forallBoolEvalFalseViaFF, forallBoolEvalFalseViaFT
        from boolOps import compose
        assert(isinstance(forallStmt, Forall))
        firstCondition = forallStmt.condition.first()
        assert(isinstance(firstCondition, In))
        assert(firstCondition.itsSet == BOOLEANS)
        varInBool = firstCondition.element
        assert varInBool in set(forallStmt.instanceVar), "To evaluate a forall statement given a condition of being in booleans, the element in question must be one of the forall instance variables."
        instanceExpr = forallStmt.instanceExpression
        P_op = Operation(P, varInBool)
        trueInstance = instanceExpr.substituted({varInBool:TRUE})
        falseInstance = instanceExpr.substituted({varInBool:FALSE})
        if trueInstance == TRUE and falseInstance == FALSE:
            # special case of Forall_{A in BOOLEANS} A
            falseEqFalse # FALSE = FALSE
            trueEqTrue # TRUE = TRUE
            evaluation = forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr}).deriveConclusion()
        else:
            # must evaluate for the TRUE and FALSE case separately
            evalTrueInstance = trueInstance.evaluate()
            evalFalseInstance = falseInstance.evaluate()
            print "evalTrueInstance", evalTrueInstance.check()
            print "evalFalseInstance", evalFalseInstance.check()
            if isinstance(evalTrueInstance, Equals) and isinstance(evalFalseInstance, Equals):
                # proper evaluations for both cases (TRUE and FALSE)
                trueCaseVal = evalTrueInstance.rhs
                falseCaseVal = evalFalseInstance.rhs
                iVar = forallStmt.instanceVar
                if trueCaseVal == TRUE and falseCaseVal == TRUE:
                    # both cases are TRUE, so the forall over booleans is TRUE
                    print evalTrueInstance.deriveViaBooleanEquality().check()
                    print evalFalseInstance.deriveViaBooleanEquality().check()
                    print compose(evalTrueInstance.deriveViaBooleanEquality(), evalFalseInstance.deriveViaBooleanEquality()).check()
                    print forallBoolEvalTrue.specialize({P_op:instanceExpr, A:iVar})
                    evaluation = forallBoolEvalTrue.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
                else:
                    # one case is FALSE, so the forall over booleans is FALSE
                    compose(evalTrueInstance, evalFalseInstance)
                    if trueCaseVal == FALSE and falseCaseVal == FALSE:
                        evaluation = forallBoolEvalFalseViaFF.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
                    elif trueCaseVal == FALSE and falseCaseVal == TRUE:
                        evaluation = forallBoolEvalFalseViaFT.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
                    elif trueCaseVal == TRUE and falseCaseVal == FALSE:
                        evaluation = forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
        return evaluation.check()
    
    def unfoldForallInSet(self, forallStmt):
        '''
        Given forall_{A in BOOLEANS} P(A), derive and return [P(TRUE) and P(FALSE)].
        '''
        from proveit.basiclogic import In, Forall
        from theorems import unfoldForallOverBool
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        return unfoldForallOverBool.specialize({Operation(P, forallStmt.instanceVar): forallStmt.instanceExpression, A:forallStmt.instanceVar}).deriveConclusion().check({forallStmt})

    def foldAsForallInSet(self, forallStmt):
        '''
        Given forall_{A in BOOLEANS} P(A), conclude and return it from [P(TRUE) and P(FALSE)].
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        '''
        from proveit.basiclogic import Forall, In
        from theorems import foldForallOverBool
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        # [P(TRUE) and P(FALSE)] => forall_{A in BOOLEANS} P(A)
        folding = foldForallOverBool.specialize({Operation(P, forallStmt.instanceVar):forallStmt.instanceExpression, A:forallStmt.instanceVar})
        folding.hypothesis.concludeViaComposition()
        return folding.deriveConclusion()

class TrueLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, 'TRUE', formatMap = {STRING:'TRUE', LATEX:r'\mathtt{TRUE}'})
    
    def evalEquality(self, other):
        from boolOps import deriveStmtEqTrue
        from theorems import trueEqTrue, trueNotFalse
        if other == TRUE:
            return deriveStmtEqTrue(trueEqTrue)
        elif other == FALSE:
            return trueNotFalse.unfold().equateNegatedToFalse()
        
class FalseLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, 'FALSE', formatMap = {STRING:'FALSE', LATEX:r'\mathtt{FALSE}'})
    
    def evalEquality(self, other):
        from boolOps import deriveStmtEqTrue
        from axioms import falseNotTrue
        from theorems import falseEqFalse
        if other == FALSE:
            return deriveStmtEqTrue(falseEqFalse)
        elif other == TRUE:
            return falseNotTrue.unfold().equateNegatedToFalse()

BOOLEANS = BooleanSet()
TRUE = TrueLiteral()
FALSE = FalseLiteral()

def inBool(X):
    from proveit.basiclogic.set.setOps import In
    return In(X, BOOLEANS)

def deduceInBool(expr):
    '''
    Attempt to deduce, then return, that the given expression is in the set of booleans.
    '''
    if hasattr(expr, 'deduceInBool'):
        return expr.deduceInBool()
    return inBool(expr)
