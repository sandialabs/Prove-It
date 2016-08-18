from proveit import Operation, Literal, USE_DEFAULTS
from proveit.common import A, P

class BooleanSet(Literal):
    def __init__(self):
        Literal.__init__(self, __package__, stringFormat='BOOLEANS', latexFormat=r'\mathbb{B}')

    def unfoldElemInSet(self, element):
        '''
        From inBool(Element), derive and return [(element = TRUE) or (element = FALSE)].
        '''
        from theorems import unfoldInBool
        #  [(element = TRUE) or (element = FALSE)] assuming inBool(element)
        return unfoldInBool.specialize({A:element}).deriveConclusion().checked({inBool(element)})
    
    def deduceElemInSet(self, element, assumptions=USE_DEFAULTS):
        '''
        Try to deduce that the given element is in the set of Booleans under the given assumptions.
        '''   
        from proveit.logic import Or, Equals
        from theorems import foldInBool
        return element.deduceInBool()
        
        
        # prerequisite = [(element = TRUE) or (element = FALSE)]
        prerequisite = Or(Equals(element, TRUE), Equals(element, FALSE))
        # [element in BOOLEANS] assuming prerequisite
        return foldInBool.specialize({A:element}).deriveConclusion().checked({prerequisite})

    def evaluateForall(self, forallStmt):
        '''
        Given a forall statement over the BOOLEANS domain, evaluate to TRUE or FALSE
        if possible.
        '''        
        from proveit.logic import Forall, Equals
        from theorems import falseEqFalse, trueEqTrue 
        from quantification.universal.theorems import forallBoolEvalTrue, forallBoolEvalFalseViaTF, forallBoolEvalFalseViaFF, forallBoolEvalFalseViaFT
        from conjunction import compose
        assert(isinstance(forallStmt, Forall)), "May only apply evaluateForall method of BOOLEANS to a forall statement"
        assert(forallStmt.domain == BOOLEANS), "May only apply evaluateForall method of BOOLEANS to a forall statement with the BOOLEANS domain"
        assert(len(forallStmt.instanceVars) == 1), "May only apply evaluateForall method of BOOLEANS to a forall statement with 1 instance variable"
        instanceVar = forallStmt.instanceVars[0]
        instanceExpr = forallStmt.instanceExpr
        P_op = Operation(P, instanceVar)
        trueInstance = instanceExpr.substituted({instanceVar:TRUE})
        falseInstance = instanceExpr.substituted({instanceVar:FALSE})
        if trueInstance == TRUE and falseInstance == FALSE:
            # special case of Forall_{A in BOOLEANS} A
            falseEqFalse # FALSE = FALSE
            trueEqTrue # TRUE = TRUE
            evaluation = forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr}).deriveConclusion()
        else:
            # must evaluate for the TRUE and FALSE case separately
            evalTrueInstance = trueInstance.evaluate().checked()
            evalFalseInstance = falseInstance.evaluate().checked()
            if isinstance(evalTrueInstance, Equals) and isinstance(evalFalseInstance, Equals):
                # proper evaluations for both cases (TRUE and FALSE)
                trueCaseVal = evalTrueInstance.rhs
                falseCaseVal = evalFalseInstance.rhs
                if trueCaseVal == TRUE and falseCaseVal == TRUE:
                    # both cases are TRUE, so the forall over booleans is TRUE
                    evalTrueInstance.deriveViaBooleanEquality().checked()
                    evalFalseInstance.deriveViaBooleanEquality().checked()
                    compose(evalTrueInstance.deriveViaBooleanEquality(), evalFalseInstance.deriveViaBooleanEquality()).checked()
                    forallBoolEvalTrue.specialize({P_op:instanceExpr, A:instanceVar})
                    evaluation = forallBoolEvalTrue.specialize({P_op:instanceExpr, A:instanceVar}).deriveConclusion()
                else:
                    # one case is FALSE, so the forall over booleans is FALSE
                    compose(evalTrueInstance, evalFalseInstance)
                    if trueCaseVal == FALSE and falseCaseVal == FALSE:
                        evaluation = forallBoolEvalFalseViaFF.specialize({P_op:instanceExpr, A:instanceVar}).deriveConclusion()
                    elif trueCaseVal == FALSE and falseCaseVal == TRUE:
                        evaluation = forallBoolEvalFalseViaFT.specialize({P_op:instanceExpr, A:instanceVar}).deriveConclusion()
                    elif trueCaseVal == TRUE and falseCaseVal == FALSE:
                        evaluation = forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr, A:instanceVar}).deriveConclusion()
        return evaluation.checked()
    
    def unfoldForall(self, forallStmt):
        '''
        Given forall_{A in Booleans} P(A), derive and return [P(TRUE) and P(FALSE)].
        '''
        from proveit.logic import Forall
        from quantification.universal.theorems import unfoldForallOverBool
        assert(isinstance(forallStmt, Forall)), "May only apply unfoldForall method of Booleans to a forall statement"
        assert(forallStmt.domain == Booleans), "May only apply unfoldForall method of Booleans to a forall statement with the Booleans domain"
        assert(len(forallStmt.instanceVars) == 1), "May only apply unfoldForall method of Booleans to a forall statement with 1 instance variable"
        return unfoldForallOverBool.specialize({Operation(P, forallStmt.instanceVars[0]): forallStmt.instanceExpr, A:forallStmt.instanceVars[0]}).deriveConclusion().checked({forallStmt})

    def foldAsForall(self, forallStmt):
        '''
        Given forall_{A in Booleans} P(A), conclude and return it from [P(TRUE) and P(FALSE)].
        '''
        from proveit.logic import Forall
        from quantification.universal.theorems import foldForallOverBool
        assert(isinstance(forallStmt, Forall)), "May only apply foldAsForall method of Booleans to a forall statement"
        assert(forallStmt.domain == Booleans), "May only apply foldAsForall method of Booleans to a forall statement with the Booleans domain"
        assert(len(forallStmt.instanceVars) == 1), "May only apply foldAsForall method of Booleans to a forall statement with 1 instance variable"
        # [P(TRUE) and P(FALSE)] => forall_{A in Booleans} P(A)
        folding = foldForallOverBool.specialize({Operation(P, forallStmt.instanceVars[0]):forallStmt.instanceExpr, A:forallStmt.instanceVars[0]})
        folding.hypothesis.concludeViaComposition()
        return folding.deriveConclusion()

class TrueLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, __package__, stringFormat='TRUE', latexFormat=r'\top')
    
    def evalEquality(self, other):
        from theorems import trueEqTrue, trueNotFalse
        if other == TRUE:
            return deriveStmtEqTrue(trueEqTrue)
        elif other == FALSE:
            return trueNotFalse.unfold().equateNegatedToFalse()
    
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        from theorems import trueInBool
        return trueInBool
        
class FalseLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, __package__, stringFormat='FALSE', latexFormat=r'\bot')
    
    def evalEquality(self, other):
        from axioms import falseNotTrue
        from theorems import falseEqFalse
        if other == FALSE:
            return deriveStmtEqTrue(falseEqFalse)
        elif other == TRUE:
            return falseNotTrue.unfold().equateNegatedToFalse()

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        from theorems import falseInBool
        return falseInBool

Booleans = BooleanSet()
TRUE = TrueLiteral()
FALSE = FalseLiteral()

def inBool(element):
    from proveit.logic.set_theory.in_set import InSet
    return InSet(element, Booleans)

def deduceInBool(expr):
    '''
    Attempt to deduce, then return, that the given expression is in the set of booleans.
    '''
    if hasattr(expr, 'deduceInBool'):
        return expr.deduceInBool()
    return inBool(expr)

def deriveStmtEqTrue(statement):
    '''
    For a given statement, derive statement = TRUE assuming statement.
    '''
    from proveit.logic import Equals
    return Equals(statement, TRUE).concludeBooleanEquality()
