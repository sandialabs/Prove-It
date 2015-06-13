import sys
from proveit.statement import *
from proveit.context import Context
from genericOperations import *
from variables import *

class BooleanSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'BOOLEANS', {MATHML:'<mstyle mathvariant="bold-double-struck"><mtext>&#x1D539;</mtext><mspace/></mstyle>', LATEX:r'\cal{B}'})

    def unfoldElemInSet(self, element):
        '''
        From inBool(Element), derive and return [(element = TRUE) or (element = FALSE)].
        '''
        #  [(element = TRUE) or (element = FALSE)] assuming inBool(element)
        return booleans.unfoldInBool.specialize({A:element}).deriveConclusion().check({inBool(element)})
    
    def deduceElemInSet(self, element):
        '''
        From [(element = TRUE) or (element = FALSE)], derive and return [element in BOOLEANS].
        '''   
        from equality import Equals
        # prerequisite = [(element = TRUE) or (element = FALSE)]
        prerequisite = Or(Equals(element, TRUE), Equals(element, FALSE))
        # [element in BOOLEANS] assuming prerequisite
        return booleans.foldInBool.specialize({A:element}).deriveConclusion().check({prerequisite})

    def evaluateForallInSet(self, forallStmt):
        '''
        Given a forall statement over the set of Booleans, evaluate to TRUE or FALSE
        if possible.
        '''
        from equality import Equals
        from sets import In
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
            booleans.falseEqFalse # FALSE = FALSE
            booleans.trueEqTrue # TRUE = TRUE
            evaluation = booleans.forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr}).deriveConclusion()
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
                    print booleans.forallBoolEvalTrue.specialize({P_op:instanceExpr, A:iVar})
                    evaluation = booleans.forallBoolEvalTrue.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
                else:
                    # one case is FALSE, so the forall over booleans is FALSE
                    compose(evalTrueInstance, evalFalseInstance)
                    if trueCaseVal == FALSE and falseCaseVal == FALSE:
                        evaluation = booleans.forallBoolEvalFalseViaFF.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
                    elif trueCaseVal == FALSE and falseCaseVal == TRUE:
                        evaluation = booleans.forallBoolEvalFalseViaFT.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
                    elif trueCaseVal == TRUE and falseCaseVal == FALSE:
                        evaluation = booleans.forallBoolEvalFalseViaTF.specialize({P_op:instanceExpr, A:iVar}).deriveConclusion()
        return evaluation.check()
    
    def unfoldForallInSet(self, forallStmt):
        '''
        Given forall_{A in BOOLEANS} P(A), derive and return [P(TRUE) and P(FALSE)].
        '''
        from sets import In
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        return booleans.unfoldForallOverBool.specialize({Operation(P, forallStmt.instanceVar): forallStmt.instanceExpression, A:forallStmt.instanceVar}).deriveConclusion().check({forallStmt})

    def foldAsForallInSet(self, forallStmt):
        '''
        Given forall_{A in BOOLEANS} P(A), conclude and return it from [P(TRUE) and P(FALSE)].
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        '''
        from sets import In
        assert(isinstance(forallStmt, Forall))
        assert(isinstance(forallStmt.condition, In))
        assert(forallStmt.condition.itsSet == BOOLEANS)
        # [P(TRUE) and P(FALSE)] => forall_{A in BOOLEANS} P(A)
        folding = booleans.foldForallOverBool.specialize({Operation(P, forallStmt.instanceVar):forallStmt.instanceExpression, A:forallStmt.instanceVar})
        folding.hypothesis.concludeViaComposition()
        return folding.deriveConclusion()

class TrueLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, 'TRUE', formatMap = {LATEX:r'\mathtt{TRUE}', MATHML:'<mstyle mathvariant="normal"><mi>true</mi></mstyle>'})
    
    def evalEquality(self, other):
        if other == TRUE:
            return deriveStmtEqTrue(booleans.trueEqTrue)
        elif other == FALSE:
            return booleans.trueNotFalse.unfold().equateNegatedToFalse()
        
class FalseLiteral(Literal):
    def __init__(self):
        Literal.__init__(self, 'FALSE', formatMap = {LATEX:r'\mathtt{FALSE}', MATHML:'<mstyle mathvariant="normal"><mi>false</mi></mstyle>'})
    
    def evalEquality(self, other):
        if other == FALSE:
            return deriveStmtEqTrue(booleans.falseEqFalse)
        elif other == TRUE:
            return booleans.falseNotTrue.unfold().equateNegatedToFalse()

# boolean related literals
literals = Literals()
BOOLEANS = literals.add(BooleanSet())
IMPLIES = literals.add('IMPLIES')
IFF = literals.add('IFF')
TRUE = literals.add(TrueLiteral())
FALSE = literals.add(FalseLiteral())
NOT = literals.add('NOT')
AND = literals.add('AND')
OR = literals.add('OR')
FORALL = literals.add('FORALL')
EXISTS = literals.add('EXISTS')
NOTEXISTS = literals.add('NOTEXISTS')

def _defineAxioms():    
    from equality import Equals, NotEquals
    from sets import Singleton, Union
    
    # TRUE is a true statement
    _firstAxiom =\
    trueAxiom = TRUE
    
    # BOOLEANS = {TRUE} union {FALSE}
    boolsDef = Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE)))
        
    # FALSE != TRUE
    falseNotTrue = NotEquals(FALSE, TRUE)
        
    # Forall statements are in the BOOLEAN set.  If it isn't TRUE, then it is FALSE.
    # forall_{P, Q**} [forall_{x** | Q**(x**)} P(x**)] in BOOLEANS
    forallInBool = Forall((P, multiQ), inBool(Forall(xStar, P_of_xStar, multiQ_of_xStar)))
    
    # If it's ever true, it can't always be not true.  (example exists = not never)
    # forall_{P, Q**} [exists_{x** | Q**(x**)} P(x**) = not[forall_{x** | Q**(x**)} (P(x**) != TRUE)]]
    existsDef = Forall((P, multiQ), Equals(Exists(xStar, P_of_xStar, multiQ_of_xStar), Not(Forall(xStar, NotEquals(P_of_xStar, TRUE), multiQ_of_xStar))))
    
    # forall_{P, Q**} notexists_{x** | Q**(x**)} P(x**) = not[exists_{x** | Q**(x**)} P(x**)]
    notExistsDef = Forall((P, multiQ), Equals(NotExists(xStar, P_of_xStar, multiQ_of_xStar), Not(Exists(xStar, P_of_xStar, multiQ_of_xStar))))
    
    # Truth table for NOT
    notF = Equals(Not(FALSE), TRUE)
    notT = Equals(Not(TRUE), FALSE)
    
    # Further defining property of NOT needed in addition to the truth table
    # because the truth table is ambiguous regarding inputs neither TRUE nor FALSE.
    
    # forall_{A} [Not(A) = TRUE] => [A=FALSE]
    implicitNotF = Forall(A, Implies(Equals(Not(A), TRUE), Equals(A, FALSE)))
    # forall_{A} [Not(A) = FALSE] => [A=TRUE]
    implicitNotT = Forall(A, Implies(Equals(Not(A), FALSE), Equals(A, TRUE)))
    
    
    # Truth table for AND
    andTT = Equals(And(TRUE, TRUE), TRUE)
    andTF = Equals(And(TRUE, FALSE), FALSE)
    andFT = Equals(And(FALSE, TRUE), FALSE)
    andFF = Equals(And(FALSE, FALSE), FALSE)
    
    # Composition of multi-And, bypassing associativity for notational convenience:
    # forall_{A, B, C**} A and B and C** = A and (B and C**)
    andComposition = Forall((A, B, multiC), Equals(And(A, B, multiC), And(A, And(B, multiC))))
    
    # A further defining property of AND is needed in addition to the truth table
    # because the truth table is ambiguous if we don't know that inputs are TRUE or FALSE:        
    # forall_{A**, B, C**} A** and B and C** => B
    andImpliesEach = Forall((multiA, B, multiC), Implies(And(multiA, B, multiC), B))
    
    # Truth table for OR
    orTT = Equals(Or(TRUE, TRUE), TRUE)
    orTF = Equals(Or(TRUE, FALSE), TRUE)
    orFT = Equals(Or(FALSE, TRUE), TRUE)
    orFF = Equals(Or(FALSE, FALSE), FALSE)
    
    # Composition of multi-Or, bypassing associativity for notational convenience:
    # forall_{A, B, C**} A or B or C** = A or (B or C**)
    orComposition = Forall((A, B, multiC), Equals(Or(A, B, multiC), Or(A, Or(B, multiC))))
    
    # forall_{A, B} (A <=> B) = [(A => B) and (B => A)]
    iffDef = Forall((A, B), Equals(Iff(A, B), And(Implies(A, B), Implies(B, A))))
    
    # forall_{A} A => (A = TRUE)
    eqTrueIntro = Forall(A, Implies(A, Equals(A, TRUE)))
    # forall_{A} (A = TRUE) => A
    eqTrueElim = Forall(A, Implies(Equals(A, TRUE), A))
    
    # (TRUE => FALSE) = FALSE
    impliesTF = Equals(Implies(TRUE, FALSE), FALSE)
    
    # forall_{A | inBool(A)} [Not(A) => FALSE] => A
    contradictoryValidation = Forall(A, Implies(Implies(Not(A), FALSE), A), inBool(A))
    # Note that implies has a deriveContradiction method that applies this axiom.
    
    return _firstAxiom, locals()

def _defineTheorems():
    from equality import Equals, NotEquals
    
    # Not(FALSE)
    _firstTheorem =\
    notFalse = Not(FALSE)
    
    # TRUE and TRUE
    trueAndTrue = And(TRUE, TRUE)
    
    # TRUE or TRUE
    trueOrTrue = Or(TRUE, TRUE)
    
    # TRUE or FALSE
    trueOrFalse = Or(TRUE, FALSE)
    
    # FALSE or TRUE
    falseOrTrue = Or(FALSE, TRUE)
    
    # TRUE = TRUE
    trueEqTrue = Equals(TRUE, TRUE)
    
    # FALSE = FALSE
    falseEqFalse = Equals(FALSE, FALSE)
    
    # forall_{A} A => (TRUE = A)
    eqTrueRevIntro = Forall(A, Implies(A, Equals(TRUE, A)))
    
    # forall_{A} (TRUE = A) => A
    eqTrueRevElim = Forall(A, Implies(Equals(TRUE, A), A))
    
    # forall_{A} Not(A) => [A=FALSE]
    notImpliesEqFalse = Forall(A, Implies(Not(A), Equals(A, FALSE)))
    
    # forall_{A} Not(A) => (FALSE = A)
    notImpliesEqFalseRev = Forall(A, Implies(Not(A), Equals(FALSE, A)))
    
    # forall_{A} Not(Not(A)) => A
    fromDoubleNegation = Forall(A, Implies(Not(Not(A)), A))
    
    # forall_{A} A => TRUE
    trueConclusion = Forall(A, Implies(A, TRUE))
    
    # forall_{A} A => A, by a trivial hypothetical reasoning
    selfImplication = Forall(A, Implies(A, A))
    
    # (TRUE => TRUE) = TRUE
    impliesTT = Equals(Implies(TRUE, TRUE), TRUE)
    
    # (FALSE => TRUE) = TRUE
    impliesFT = Equals(Implies(FALSE, TRUE), TRUE)

    # (FALSE => FALSE) = TRUE
    impliesFF = Equals(Implies(FALSE, FALSE), TRUE)

    # forall_{A, B} (A <=> B) => (A => B)
    iffImpliesRight = Forall((A, B), Implies(Iff(A, B), Implies(A, B)))
    
    # forall_{A, B} (A <=> B) => (B => A)
    iffImpliesLeft = Forall((A, B), Implies(Iff(A, B), Implies(B, A)))
    
    # forall_{A, B} (A <=> B) => (B <=> A)
    iffSymmetry = Forall((A, B), Implies(Iff(A, B), Iff(B, A)))
    
    # forall_{A, B, C} (A <=> B and B <=> C) => (A <=> C)
    iffTransitivity = Forall((A, B, C), Implies(And(Iff(A, B), Iff(B, C)), Iff(A, C)))
    
    # Not(TRUE) => FALSE
    notTimpliesF = Implies(Not(TRUE), FALSE)

    # (TRUE <=> TRUE) = TRUE
    iffTT = Equals(Iff(TRUE, TRUE), TRUE)

    # (FALSE <=> FALSE) = TRUE
    iffFF = Equals(Iff(FALSE, FALSE), TRUE)

    # (TRUE <=> FALSE) = FALSE
    iffTF = Equals(Iff(TRUE, FALSE), FALSE)
    
    # (FALSE <=> TRUE) = FALSE
    iffFT = Equals(Iff(FALSE, TRUE), FALSE)
    
    # forall_{A | A, B | B} (A and B)
    conjunctionIntro = Forall((A, B), And(A, B), (A, B))

    # forall_{A} inBool(A) => (A=TRUE or A=FALSE)
    unfoldInBool = Forall(A, Implies(inBool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))

    # forall_{A} (A=TRUE or A=FALSE) => inBool(A)
    foldInBool = Forall(A, Implies(Or(Equals(A, TRUE), Equals(A, FALSE)), inBool(A)))
    
    # forall_{A} Not(A) => [A => FALSE]
    contradictionFromNegation = Forall(A, Implies(Not(A), Implies(A, FALSE)))

    # forall_{A} (A=FALSE) => Not(A)
    notFromEqFalse = Forall(A, Implies(Equals(A, FALSE), Not(A)))

    # forall_{A} (FALSE=A) => Not(A)
    notFromEqFalseRev = Forall(A, Implies(Equals(FALSE, A), Not(A)))

    # forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
    notOrFromNeither = Forall((A, B), Implies(Not(A), Implies(Not(B), Not(Or(A, B)))))

    # forall_{A, B | Not(A), Not(B)} (A or B) => FALSE
    orContradiction = Forall((A, B), Implies(Or(A, B), FALSE), (Not(A), Not(B)))

    # forall_{A, B | inBool(A), Not(B)} (A or B) => A
    orImpliesLeftIfNotRight = Forall((A, B), Implies(Or(A, B), A), (inBool(A), Not(B)))
    
    # forall_{A, B | Not(A), inBool(B)} (A or B) => B
    orImpliesRightIfNotLeft = Forall((A, B), Implies(Or(A, B), B), (Not(A), inBool(B)))

    # forall_{A} A => Not(Not(A))
    doubleNegation = Forall(A, Implies(A, Not(Not(A))))

    # forall_{A} A => [Not(A)=FALSE]
    eqFalseFromNegation = Forall(A, Implies(A, Equals(Not(A), FALSE)))

    # forall_{A} A => [FALSE=Not(A)]
    eqFalseRevFromNegation = Forall(A, Implies(A, Equals(FALSE, Not(A))))

    # forall_{A | inBool(A)} (A != FALSE) => A
    fromNotFalse = Forall(A, Implies(NotEquals(A, FALSE), A), inBool(A))

    # forall_{A, B | inBool(B)} [Not(B) => Not(A)] => [A=>B] 
    transpositionFromNegated = Forall((A, B), Implies(Implies(Not(B), Not(A)), Implies(A, B)), inBool(B))

    # forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
    doubleNegateConclusion = Forall((A, B), Implies(Implies(A, B), Implies(A, Not(Not(B)))), inBool(B))

    # forall_{A, B | inBool(A), inBool(B)} [Not(B) => A] => [Not(A)=>B] 
    transpositionFromNegatedHypothesis = Forall((A, B), Implies(Implies(Not(B), A), Implies(Not(A), B)), (inBool(A), inBool(B)))

    # forall_{A, B | inBool(B)} [B => Not(A)] => [A=>Not(B)] 
    transpositionFromNegatedConclusion = Forall((A, B), Implies(Implies(B, Not(A)), Implies(A, Not(B))), inBool(B))

    # forall_{A, B | inBool(A), inBool(B)} [B=>A] => [Not(A) => Not(B)] 
    transpositionToNegated = Forall((A, B), Implies(Implies(B, A), Implies(Not(A), Not(B))), (inBool(A), inBool(B)))

    # TRUE != FALSE
    trueNotFalse = NotEquals(TRUE, FALSE)

    # forall_{A} A => (A != FALSE)
    notEqualsFalse = Forall(A, Implies(A, NotEquals(A, FALSE)))

    # inBool(TRUE)
    trueInBool = inBool(TRUE)

    # inBool(FALSE)
    falseInBool = inBool(FALSE)

    # forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
    unfoldForallOverBool = Forall(P, Implies(Forall(A, PofA, inBool(A)), And(PofTrue, PofFalse)))

    # forall_{A} A=TRUE => inBool(A)
    inBoolIfEqTrue = Forall(A, Implies(Equals(A, TRUE), inBool(A)))

    # forall_{A} TRUE=A => inBool(A)
    inBoolIfEqTrueRev = Forall(A, Implies(Equals(TRUE, A), inBool(A)))

    # forall_{A} A=FALSE => inBool(A)
    inBoolIfEqFalse = Forall(A, Implies(Equals(A, FALSE), inBool(A)))

    # forall_{A} FALSE=A => inBool(A)
    inBoolIfEqFalseRev = Forall(A, Implies(Equals(FALSE, A), inBool(A)))

    # forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
    hypotheticalDisjunction = Forall((A, B, C), Implies(And(Implies(A, C), Implies(B, C)), Implies(Or(A, B), C)), (inBool(A), inBool(B), inBool(C)))

    # forall_{P} [P(TRUE) and P(FALSE)] => [forall_{A in BOOLEANS} P(A)]
    foldForallOverBool = Forall(P, Implies(And(PofTrue, PofFalse), Forall(A, PofA, inBool(A))))

    # forall_{P} [P(TRUE) and P(FALSE)] => {[forall_{A in BOOLEANS} P(A)] = TRUE}
    forallBoolEvalTrue = Forall(P, Implies(And(PofTrue, PofFalse), Equals(Forall(A, PofA, inBool(A)), TRUE)))

    # forall_{P, Q**, R**} [forall_{x** | Q**(x)} forall_{y** | R**(y**)} P(x**, y**)] => forall_{x**, y** | Q**(x), R**(y**)} P(x**, y**)
    forallBundling = Forall((P, multiQ, multiR), Implies(Forall(xStar, Forall(yStar, P_of_xStar_yStar, multiR_of_yStar), multiQ_of_xStar), Forall((xStar, yStar), P_of_xStar_yStar, (multiQ_of_xStar, multiR_of_yStar))))

    # forall_{P, Q**, R**} forall_{x**, y** | Q**(x), R**(y**)} P(x**, y**) => forall_{x** | Q**(x)} forall_{y** | R**(y**)} P(x, y**) 
    forallUnravelling = Forall((P, multiQ, multiR), Implies(Forall((xStar, yStar), P_of_xStar_yStar, (multiQ_of_xStar, multiR_of_yStar)), Forall(xStar, Forall(yStar, P_of_xStar_yStar, multiR_of_yStar), multiQ_of_xStar)))

    # forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
    iffOverBoolImplEq = Forall((A, B), Implies(Iff(A, B), Equals(A, B)), (inBool(A), inBool(B)))

    # forall_{A in booleans} A = Not(Not(A))
    doubleNegationEquiv = Forall(A, Equals(A, Not(Not(A))), inBool(A))

    # forall_{P, Q**, R**} forall_{x**, y** | Q**(x), R**(y**)} P(x**, y**) = forall_{x** | Q**(x)} forall_{y** | R**(y**)} P(x, y**) 
    forallBundledEquiv = Forall((P, multiQ, multiR), Equals(Forall((xStar, yStar), P_of_xStar_yStar, (multiQ_of_xStar, multiR_of_yStar)), Forall(xStar, Forall(yStar, P_of_xStar_yStar, multiR_of_yStar), multiQ_of_xStar)))

    # forall_{P, Q**} [forall_{x** | Q**(x**)} P(x**)] = [forall_{x** | Q**(x**)} {P(x**)=TRUE}]
    forallEqTrueEquiv = Forall((P, multiQ), Equals(Forall(xStar, P_of_xStar, multiQ_of_xStar), Forall(xStar, Equals(P_of_xStar, TRUE), multiQ_of_xStar)))
    
    # forall_{A in BOOLEANS, B in BOOLEANS} (A => B) in BOOLEANS                                                                                                        
    implicationClosure = Forall((A, B), inBool(Implies(A, B)), (inBool(A), inBool(B)))

    # forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) in BOOLEANS                                                                                                        
    iffClosure = Forall((A, B), inBool(Iff(A, B)), (inBool(A), inBool(B)))

    # forall_{A in BOOLEANS, B in BOOLEANS} (A and B) in BOOLEANS                                                                                                        
    conjunctionClosure = Forall((A, B), inBool(And(A, B)), (inBool(A), inBool(B)))

    # forall_{A in BOOLEANS, B in BOOLEANS} (A or B) in BOOLEANS                                                                                                        
    disjunctionClosure = Forall((A, B), inBool(Or(A, B)), (inBool(A), inBool(B)))

    # forall_{A in BOOLEANS} Not(A) in BOOLEANS                                                                                                        
    negationClosure = Forall(A, inBool(Not(A)), inBool(A))

    # forall_{A in BOOLEANS} [A => FALSE] => Not(A)                                            
    hypotheticalContradiction = Forall(A, Implies(Implies(A, FALSE), Not(A)), inBool(A)) 

    # forall_{P, Q**} [notexists_{x** | Q**(x**)} P(x**) = forall_{x** | Q**(x**)} (P(x**) != TRUE)]
    existsDefNegation = Forall((P, multiQ), Equals(NotExists(xStar, P_of_xStar, multiQ_of_xStar), Forall(xStar, NotEquals(P_of_xStar, TRUE), multiQ_of_xStar)))
    
    # forall_{P, Q**} notexists_{x** | Q**(x**)} P(x**) => Not(exists_{x** | Q**(x**)} P(x**))
    notExistsUnfolding = Forall((P, multiQ), Implies(NotExists(xStar, P_of_xStar, multiQ_of_xStar), Not(Exists(xStar, P_of_xStar, multiQ_of_xStar))))
    
    # forall_{P, Q**} Not(Exists_{x** | Q**(x**)} P(x**)) => NotExists_{x** | Q**(x**)} P(x**)
    notExistsFolding = Forall((P, multiQ), Implies(Not(Exists(xStar, P_of_xStar, multiQ_of_xStar)), NotExists(xStar, P_of_xStar, multiQ_of_xStar)))

    # forall_{P, Q**} [exists_{x** | Q**(x**)} P(x**)] in BOOLEANS
    existsInBool = Forall((P, multiQ), inBool(Exists(xStar, P_of_xStar, multiQ_of_xStar)))

    # forall_{P, Q**} forall_{x** | Q**(x**)} [P(x**) => exists_{y** | Q(y**)} P(y**)]
    existenceByExample = Forall((P, multiQ), Forall(xStar, Implies(P_of_xStar, Exists(yStar, P_of_yStar, multiQ_of_yStar)), multiQ_of_xStar))
    
    # forall_{P, Q**} [exists_{x** | Q**(x**)} Not(P(x**))] => [Not(forall_{x** | Q**(x**)} P(x**)]
    existsNotImpliesNotForall = Forall((P, multiQ), Implies(Exists(xStar, Not(P_of_xStar), multiQ_of_xStar), Not(Forall(xStar, P_of_xStar, multiQ_of_xStar))))
    
    # forall_{P, Q**} forall_{x** | Q**(x**)} P(x**) => NotExists_{x** | Q**(x**)} Not(P(x**))
    forallImpliesNotExistsNot = Forall((P, multiQ), Implies(Forall(xStar, P_of_xStar, multiQ_of_xStar), NotExists(xStar, Not(P_of_xStar), multiQ_of_xStar)))

    # forall_{P} [(P(TRUE) = PofTrueVal) and (P(FALSE) = PofFalseVal)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}, assuming PofTrueVal=FALSE or PofFalseVal=FALSE
    def _forallBoolEvalFalse(PofTrueVal, PofFalseVal):
        return Forall(P, Implies(And(Equals(PofTrue, PofTrueVal), Equals(PofFalse, PofFalseVal)), Equals(Forall(A, PofA, inBool(A)), FALSE)))
    forallBoolEvalFalseViaFF = _forallBoolEvalFalse(FALSE, FALSE)
    forallBoolEvalFalseViaFT = _forallBoolEvalFalse(FALSE, TRUE)
    forallBoolEvalFalseViaTF = _forallBoolEvalFalse(TRUE, FALSE)
    
    return _firstTheorem, locals()
    
booleans = Context(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)
        
PofTrue = Operation(P, [TRUE])
PofFalse = Operation(P, [FALSE])

class Forall(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions = None):
        '''
        Create a Forall expression:
        forall_{instanceVar | condition} instanceExpression.
        This expresses that the instanceExpression is true for all values of the instanceVar(s)
        given that the optional condition(s) is/are satisfied.  The instanceVar(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, FORALL, instanceVars, instanceExpression, conditions)
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'forall'
        elif formatType == LATEX:
            return r'\forall'
        elif formatType == MATHML:
            return '<mo>&#x2200;</mo>'

    def specialize(self, subMap=None, conditionAsHypothesis=False):
        '''
        From this Forall expression, and the condition if there is one,
        derive and return a specialized form.  If conditionAsHypothesis is True, 
        derive and return the implication with the condition as hypothesis 
        and specialized form as the conclusion.
        '''
        specialized = Expression.specialize(self, subMap)
        if conditionAsHypothesis and self.hasCondition():
            return Implies(self.condition, specialized).check({self})
        return specialized
    
    def equateMaps(self):
        '''
        From forall_{x | Q(x)} f(x) = g(x) derive and return 
        [x -> f(x) | Q(x)] = [x -> g(x) | Q(x)]
        '''
        from mapping import mapping, f, g
        from equality import Equals
        assert isinstance(self.instanceExpression, Equals), "Instance expression must be an equality to use mapSubstitution"
        fOp, fOpSub = Operation(f, self.instanceVar), self.instanceExpression.lhs
        gOp, gOpSub = Operation(g, self.instanceVar), self.instanceExpression.rhs
        Q_op, Q_op_sub = Operation(Q, self.instanceVar), self.condition
        if self.hasCondition():
            return mapping.mapSubstitution.specialize({fOp:fOpSub, gOp:gOpSub, Q_op:Q_op_sub, x:self.instanceVar, y:self.instanceVar}).deriveConclusion().check({self})
        else:
            return mapping.mapOverAllSubstitution.specialize({fOp:fOpSub, gOp:gOpSub}).deriveConclusion().check({self})
    
    def unfold(self):
        '''
        From this forall statement, derive an "unfolded" version dependent upon the condition of the forall,
        calling unfoldForall on the condition.
        For example, from forall_{A in BOOLEANS} P(A), derives P(TRUE) and P(FALSE).
        '''    
        return self.condition.unfoldForall(self)
    
    def equateWithUnfolded(self):
        pass
        
    def concludeAsFolded(self):
        '''
        Conclude this forall statement from an "unfolded" version dependent upon the condition of the forall,
        calling foldAsForall on the condition.
        For example, conclude forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''    
        return self.condition.foldAsForall(self)
    
    def deriveBundled(self):
        '''
        From a nested forall statement, derive the bundled forall statement.  For example,
        forall_{x | Q(x)} forall_{y | R(y)} P(x, y) becomes forall_{x, y | Q(x), R(y)} P(x, y).
        '''
        assert isinstance(self.instanceExpression, Forall), "Can only bundle nested forall statements"
        innerForall = self.instanceExpression
        composedInstanceVars = ExpressionList([self.instanceVar, innerForall.instanceVar])
        P_op, P_op_sub = Operation(P, composedInstanceVars), innerForall.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        multiR_op, multiR_op_sub = Operation(multiR, innerForall.instanceVar), innerForall.condition
        return booleans.forallBundling.specialize({xStar:self.instanceVar, yStar:innerForall.instanceVar, P_op:P_op_sub, multiQ_op:multiQ_op_sub, multiR_op:multiR_op_sub}).deriveConclusion().check({self})

    def _specializeUnravellingTheorem(self, theorem, *instanceVarLists):
        print instanceVarLists
        assert len(self.instanceVar) > 1, "Can only unravel a forall statement with multiple instance variables"
        if len(instanceVarLists) == 1:
            raise ValueError("instanceVarLists should be a list of 2 or more Variable lists")
        if len(instanceVarLists) > 2:
            return self.deriveUnravelled(ExpressionList(instanceVarLists[:-1]), instanceVarLists[-1]).deriveUnravelled(*instanceVarLists[:-1]).check({self})
        outerVars, innerVars = instanceVarLists
        outerVarSet, innerVarSet = set(outerVars), set(innerVars)
        assert innerVarSet | outerVarSet == set(self.instanceVar), "outerVars and innterVars must combine to the full set of instance variables"
        assert innerVarSet.isdisjoint(outerVarSet), "outerVars and innterVars must be disjoint sets"
        innerConditions = []
        outerConditions = []
        for condition in self.condition:
            if condition.freeVars().isdisjoint(innerVars):
                outerConditions.append(condition)
            else: innerConditions.append(condition)
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, outerVars), outerConditions
        multiR_op, multiR_op_sub = Operation(multiR, innerVars), innerConditions
        print P_op_sub
        print multiQ_op_sub
        print multiR_op_sub
        return theorem.specialize({xStar:outerVars, yStar:innerVars, P_op:P_op_sub, multiQ_op:multiQ_op_sub, multiR_op:multiR_op_sub}) 
           
    def deriveUnravelled(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive the nested, unravelled forall statement.  For example,
        forall_{x, y | Q(x), R(y)} P(x, y) becomes forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        return self._specializeUnravellingTheorem(booleans.forallUnravelling, *instanceVarLists).deriveConclusion().check({self})

    def deriveUnravelledEquiv(self, *instanceVarLists):
        '''
        From a multi-variable forall statement, derive its equivalence with a nested, unravelled forall statement.
        For example, forall_{x, y | Q(x), R(y)} P(x, y) = forall_{x | Q(x)} forall_{y | R(y)} P(x, y).
        The instanceVarLists should be a list of lists of instanceVars, in the same order as the original
        instanceVars, to indicate how to break up the nested forall statements.
        '''
        return self._specializeUnravellingTheorem(booleans.forallBundledEquiv, *instanceVarLists).check()
        
    def evaluate(self):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if possible
        by calling the condition's evaluateForall method
        '''
        assert self.hasCondition(), "Cannot evaluate a forall statement with no conditions"
        if len(self.instanceVar) == 1:
            # start with the first condition which may then nest over subsequent conditions
            return _evaluate(self, lambda : self.condition.evaluateForall(self))
        else:
            # Evaluate an unravelled version
            unravelledEquiv = self.deriveUnravelledEquiv(*[condition.freeVars() for condition in self.condition]).check()
            unravelledEval = unravelledEquiv.rhs.evaluate()
            return unravelledEquiv.applyTransitivity(unravelledEval).check()            

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this forall expression is in the set of BOOLEANS,
        as all forall expressions are (they are taken to be false when not true).
        '''
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        return booleans.forallInBool.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).check()

Operation.registerOperation(FORALL, lambda operand : Forall(operand.argument, operand.expression, operand.domainCondition))

class Exists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVar | condition} instanceExpression
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpression is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, EXISTS, instanceVars, instanceExpression, conditions)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'exists'
        elif formatType == LATEX:
            return r'\exists'
        elif formatType == MATHML:
            return '<mo>&#x2203;</mo>'

    def concludeViaExample(self, exampleInstance):
        '''
        Conclude and return this [exists_{y | Q(x)} P(y)] from P(x) and Q(x), where x is the given exampleInstance.
        '''
        # P(x) where x is the given exampleInstance
        exampleExpr = self.instanceExpression.substituted({self.instanceVar:exampleInstance})
        # Q(x) where x is the given exampleInstance
        exampleCondition = self.condition.substituted({self.instanceVar:exampleInstance})
        # forall_{P, Q} forall_{x | Q(x)} [P(x) => exists_{y | Q(x)} P(y)]
        return booleans.existenceByExample.specialize({Operation(P, self.instanceVar): self.instanceExpression, Operation(multiQ, self.instanceVar): self.condition, yStar:self.instanceVar}).specialize({xStar:exampleInstance}).deriveConclusion().check({exampleExpr, exampleCondition})

    def deriveNegatedForall(self):
        '''
        From [exists_{x** | Q**(x**)} Not(P(x**))], derive and return Not(forall_{x** | Q**(x**)} P(x**)).
        From [exists_{x** | Q**(x**)} P(x**)], derive and return Not(forall_{x** | Q**(x**)} (P(x**) != TRUE)).
        '''
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        if isinstance(self.instanceExpression, Not):
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression.operand
            return booleans.existsNotImpliesNotForall.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveConclusion().check({self})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
            return booleans.existsDef.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveRightViaEquivalence().check({self})
    
    def deduceInBool(self):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        return booleans.existsInBool.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).check()

Operation.registerOperation(EXISTS, lambda operand : Exists(operand.argument, operand.expression, operand.domainCondition))

class NotExists(OperationOverInstances):
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVar | condition} instanceExpression
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpression is true.  The instanceVar(s) and condition(s) may be 
        singular or plural (iterable).
        '''
        OperationOverInstances.__init__(self, NOTEXISTS, instanceVars, instanceExpression, conditions)

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'notexist'
        elif formatType == LATEX:
            return r'\nexists'
        elif formatType == MATHML:
            return '<mo>&#x2204;</mo>'
        
    def unfold(self):
        '''
        Deduce and return Not(Exists_{x** | Q**(x**)} P(x**)) from NotExists_{x** | Q**(x**)} P(x**)
        '''
        Q_op, Q_op_sub = Operation(multiQ, self.instanceVar), self.condition
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        return booleans.notExistsUnfolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xStar:self.instanceVar}).deriveConclusion().check({self})
    
    def concludeAsFolded(self):
        '''
        Prove and return some NotExists_{x** | Q**(x**)} P(x**) assuming Not(Exists_{x** | Q**(x**)} P(x**)).
        '''
        Q_op, Q_op_sub = Operation(multiQ, self.instanceVar), self.condition
        P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
        folding = booleans.notExistsFolding.specialize({P_op:P_op_sub, Q_op:Q_op_sub, xStar:self.instanceVar})
        return folding.deriveConclusion().check({self.unfold()})
    
    def concludeViaForall(self):
        '''
        Prove and return either some NotExists_{x** | Q**(x**)} Not(P(x**)) or NotExists_{x** | Q**(x**)} P(x**)
        assumint forall_{x** | Q**(x**)} P(x**) or assuming forall_{x** | Q**(x**)} (P(x) != TRUE) respectively.
        '''
        from equality import NotEquals
        multiQ_op, multiQ_op_sub = Operation(multiQ, self.instanceVar), self.condition
        operand = self.operand
        if isinstance(self.instanceExpression, Not):
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression.operand
            assumption = Forall(operand.argument, operand.expression.operand, operand.domainCondition)
            return booleans.forallImpliesNotExistsNot.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveConclusion().check({assumption})
        else:
            P_op, P_op_sub = Operation(P, self.instanceVar), self.instanceExpression
            assumption = Forall(operand.argument, NotEquals(operand.expression, TRUE), operand.domainCondition)
            return booleans.existsDefNegation.specialize({P_op:P_op_sub, multiQ_op:multiQ_op_sub, xStar:self.instanceVar}).deriveLeftViaEquivalence().check({assumption})

Operation.registerOperation(NOTEXISTS, lambda operand : NotExists(operand.argument, operand.expression, operand.domainCondition))
    
class Implies(BinaryOperation):
    def __init__(self, hypothesis, conclusion):
        BinaryOperation.__init__(self, IMPLIES, hypothesis, conclusion)
        self.hypothesis = hypothesis
        self.conclusion = conclusion

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '=>'
        elif formatType == LATEX:
            return r'\Rightarrow'
        elif formatType == MATHML:
            return '<mo>&#x21D2;</mo>'

    def deriveConclusion(self):
        r'''
        From :math:`(A \Rightarrow B)` derive and return :math:`B` assuming :math:`A`.
        '''
        return self.conclusion.check({self, self.hypothesis})
                
    def applySyllogism(self, otherImpl):
        '''
        From :math:`A \Rightarrow B` (self) and a given :math:`B \Rightarrow C` (otherImpl), derive and return :math:`A \Rightarrow C`.
        '''
        assert isinstance(otherImpl, Implies), "expected an Implies object"
        if self.conclusion == otherImpl.hypothesis:
            return Implies(self.hypothesis, otherImpl.conclusion).check({self, otherImpl})
        elif self.hypothesis == otherImpl.conclusion:
            return Implies(otherImpl.hypothesis, self.conclusion).check({self, otherImpl})
    
    def deriveViaContradiction(self):
        r'''
        From :math:`[\lnot A \Rightarrow \mathtt{FALSE}]`, derive and return :math:`A` assuming :math:`A \in \mathcal{B}`.
        Or from :math:`[A \Rightarrow \mathtt{FALSE}]`, derive and return :math:`\lnot A` assuming :math:`A \in \mathcal{B}`.
        '''
        assert self.conclusion == FALSE
        if isinstance(self.hypothesis, Not):
            stmt = self.hypothesis.operand
            return booleans.contradictoryValidation.specialize({A:stmt}).deriveConclusion().check({self, inBool(stmt)})
        else:
            return booleans.hypotheticalContradiction.specialize({A:self.hypothesis}).deriveConclusion().check({self, inBool(self.hypothesis)})
    
    def generalize(self, newForallVars, newConditions=tuple()):
        r'''
        This makes a generalization of this expression, prepending Forall 
        operations according to newForallVars and newConditions that will bind
        'arbitrary' free variables.  This overrides the Expression version
        to absorb hypothesis into conditions if they match.  For example, 
        :math:`[A(x) \Rightarrow [B(x, y) \Rightarrow P(x, y)]]` generalized 
        forall :math:`x, y` such that :math:`A(x), B(x, y)`
        becomes :math:`\forall_{x, y | A(x), B(x, y)} P(x, y)`,
        '''
        hypothesizedConditions = set()
        newConditionsSet = set(newConditions)
        expr = self
        while isinstance(expr, Implies) and expr.hypothesis in newConditionsSet:
            hypothesizedConditions.add(expr.hypothesis)
            expr = expr.conclusion
        if len(hypothesizedConditions) == 0:
            # Just use the Expression version
            return Expression.generalize(self, newForallVars, newConditions)
        return Expression.generalize(expr, newForallVars, newConditions)
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
        if isinstance(self.hypothesis, Not) and isinstance(self.conclusion, Not):
            return booleans.transpositionFromNegated.specialize({B:self.hypothesis.operand, A:self.conclusion.operand}).check({inBool(self.hypothesis.operand)})
        elif isinstance(self.hypothesis, Not):
            return booleans.transpositionFromNegatedHypothesis.specialize({B:self.hypothesis.operand, A:self.conclusion}).check({inBool(self.hypothesis.operand), inBool(self.conclusion)})
        elif isinstance(self.conclusion, Not):
            return booleans.transpositionFromNegatedConclusion.specialize({B:self.hypothesis, A:self.conclusion.operand}).check({inBool(self.hypothesis)})
        else:
            return booleans.transpositionToNegated.specialize({B:self.hypothesis, A:self.conclusion}).check({inBool(self.hypothesis), inBool(self.conclusion)})
        
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
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.impliesTT
            elif A == TRUE and B == FALSE: return booleans.impliesTF
            elif A == FALSE and B == TRUE: return booleans.impliesFT
            elif A == FALSE and B == FALSE: return booleans.impliesFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))
    
    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this implication expression is in the set of BOOLEANS.
        '''
        hypothesisInBool = deduceInBool(self.hypothesis)
        conclusionInBool = deduceInBool(self.conclusion)
        return booleans.implicationClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({hypothesisInBool, conclusionInBool})

Operation.registerOperation(IMPLIES, lambda operands : Implies(*operands))

class Not(Operation):
    def __init__(self, A):
        Operation.__init__(self, NOT, A)
        self.operand = A

    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'not'
        if formatType == LATEX:
            return r'\lnot'
        elif formatType == MATHML:
            return '<mo>&#x00AC;</mo>'

    def formatted(self, formatType, fenced=False):
        if formatType == STRING:
            return Operation.formatted(self, formatType, fenced)                    
        elif formatType == LATEX:
            outStr = ''
            if fenced: outStr += "("
            outStr += self.formattedOperator(formatType) + ' ' + self.operand.formatted(formatType, fenced=True)
            if fenced: outStr += ')'
            return outStr            
        elif formatType == MATHML:
            outStr = ''
            if fenced: outStr += "<mfenced separators=''>"
            outStr += '<mrow>' + self.formattedOperator(formatType) + self.operand.formatted(formatType, fenced=True) + '</mrow>'
            if fenced: outStr += '</mfenced>'
            return outStr
        
    def evaluate(self):
        '''
        Given an operand that evaluates to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        from equality import Equals
        if self.operand == TRUE: return booleans.notT
        elif self.operand == FALSE: return booleans.notF
        def doEval():
            operandEval = self.operand.evaluate()
            if operandEval.rhs == TRUE: 
                val = booleans.notT.rhs
            elif operandEval.rhs == FALSE: 
                val = booleans.notF.rhs
            return operandEval.lhsSubstitute(A, Equals(Not(A), val))
        return _evaluate(self, doEval)

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'not' expression is in the set of BOOLEANS.
        '''
        operandInBool = deduceInBool(self.operand)
        return booleans.negationClosure.specialize({A:self.operand}).check({operandInBool})
   
    def equateNegatedToFalse(self):
        r'''
        From :math:`\lnot A`, derive and return :math:`A = \mathtt{FALSE}`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        return booleans.notImpliesEqFalse.specialize({A:self.operand}).deriveConclusion().check({self})

    def equateFalseToNegated(self):
        r'''
        From :math:`\lnot A`, derive and return :math:`\mathtt{FALSE} = A`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        return booleans.notImpliesEqFalseRev.specialize({A:self.operand}).deriveConclusion().check({self})
    
    def deriveViaDoubleNegation(self):
        r'''
        From :math:`\lnot \lnot A`, derive and return :math:`A` assuming :math:`A \in \mathcal{B}`.
        Note, see Equals.deriveViaBooleanEquality for the reverse process.
        '''
        if isinstance(self.operand, Not):
            return booleans.fromDoubleNegation.specialize({A:self.operand.operand}).deriveConclusion().check({self, inBool(A)})

    def concludeViaDoubleNegation(self):
        r'''
        Prove and return self of the form :math:`\lnot \lnot A` assuming :math:`A`.
        Also see version in NotEquals for :math:`A \neq \mathtt{FALSE}`.
        '''
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return booleans.doubleNegation.specialize({A:stmt}).deriveConclusion().check({stmt})
            
    def deriveContradiction(self):
        r'''
        From :math:`\lnot A`, derive and return :math:`A \Rightarrow \mathtt{FALSE}`.
        '''
        return booleans.contradictionFromNegation.specialize({A:self.operand}).check({self})
    
    def deriveNotEquals(self):
        r'''
        From :math:`\lnot(A = B)`, derive and return :math:`A \neq B`.
        '''
        from equality import equality, Equals
        if isinstance(self.operand, Equals):
            return equality.foldNotEquals.specialize({x:self.operand.lhs, y:self.operand.rhs}).deriveConclusion().check({self})

    def deriveNotExists(self):
        r'''
        From :math:`\lnot \exists_{x** | Q**(x**)} P(x**)`, derive and return :math:`\nexists_{x** | Q**(x**)} P(x**)`
        '''
        operand = self.operand
        if isinstance(operand, Exists):
            exOperand = operand.operand # Exist's operand
            notExistsExpr = NotExists(exOperand.argument, exOperand.expression, exOperand.domainCondition)
            return notExistsExpr.concludeAsFolded().check({self})
        
    def deduceDoubleNegationEquiv(self):
        '''
        For some Not(Not(A)), derive and return A = Not(Not(A)) assuming A in BOOLEANS.
        '''
        if isinstance(self.operand, Not):
            Asub = self.operand.operand
            return booleans.doubleNegationEquiv.specialize({A:Asub}).check({inBool(Asub)})

Operation.registerOperation(NOT, lambda operand : Not(operand))
        
class And(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        AssociativeOperation.__init__(self, AND, *operands)

    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
            return 'and'
        elif formatType == MATHML:
            return '<mo>&#x2227;</mo>'
        elif formatType == LATEX:
            return r'\land'
        
    def deriveInPart(self, indexOrExpr):
        r'''
        From :math:`(A \land ... \land X \land ... \land Z)` derive :math:`X`.  indexOrExpr specifies 
        :math:`X` either by index or the Expression.
        '''
        idx = indexOrExpr if isinstance(indexOrExpr, int) else list(self.operand).index(indexOrExpr)
        return booleans.andImpliesEach.specialize({multiA:self.operands[:idx], B:self.operands[idx], multiC:self.operands[idx+1:]}).deriveConclusion().check({self})
        
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
        compose(*self.operands)
            
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        if len(self.operands) >= 3:
            # A and B and C** = A and (B and C**)
            compositionEquiv = booleans.andComposition.specialize({A:self.operands[0], B:self.operands[1], multiC:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.andTT
            elif A == TRUE and B == FALSE: return booleans.andTF
            elif A == FALSE and B == TRUE: return booleans.andFT
            elif A == FALSE and B == FALSE: return booleans.andFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'and' expression is in the set of BOOLEANS.
        '''
        leftInBool = deduceInBool(self.leftOperand)
        rightInBool = deduceInBool(self.rightOperand)
        return booleans.conjunctionClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({leftInBool, rightInBool})

Operation.registerOperation(AND, lambda operands : And(*operands))

class Or(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Or together any number of operands: A or B or C
        '''
        AssociativeOperation.__init__(self, OR, *operands)
    
    def formattedOperator(self, formatType):
        '''
        Formatted operator when there are 2 or more operands.
        '''
        if formatType == STRING:
            return 'or'
        if formatType == LATEX:
            return r'\lor'
        elif formatType == MATHML:
            return '<mo>&#x2228;</mo>'

    def deriveRightIfNotLeft(self):
        '''
        From (A or B) derive and return B assuming Not(A), inBool(B). 
        '''
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return booleans.orImpliesRightIfNotLeft.specialize({A:leftOperand, B:rightOperand}).deriveConclusion().check({self, Not(leftOperand), inBool(rightOperand)})

    def deriveLeftIfNotRight(self):
        '''
        From (A or B) derive and return A assuming inBool(A), Not(B).
        '''
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        return booleans.orImpliesLeftIfNotRight.specialize({A:leftOperand, B:rightOperand}).deriveConclusion().check({self, Not(rightOperand), inBool(leftOperand)})
        
    def deriveCommonConclusion(self, conclusion):
        '''
        From (A or B) derive and return the provided conclusion C assuming A=>C, B=>C, A,B,C in BOOLEANS.
        '''
        # forall_{A in Bool, B in Bool, C in Bool} (A=>C and B=>C) => ((A or B) => C)
        assert len(self.operands) == 2
        leftOperand, rightOperand = self.operands
        leftImplConclusion = Implies(leftOperand, conclusion)
        rightImplConclusion = Implies(rightOperand, conclusion)
        # (A=>C and B=>C) assuming A=>C, B=>C
        compose(leftImplConclusion, rightImplConclusion)
        return booleans.hypotheticalDisjunction.specialize({A:leftOperand, B:rightOperand, C:conclusion}).deriveConclusion().deriveConclusion().check({self, leftImplConclusion, rightImplConclusion, inBool(A), inBool(B), inBool(C)})
        
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        if len(self.operands) >= 3:
            # A or B or C** = A or (B or C**)
            compositionEquiv = booleans.orComposition.specialize({A:self.operands[0], B:self.operands[1], multiC:self.operands[2:]})
            decomposedEval = compositionEquiv.rhs.evaluate()
            return compositionEquiv.applyTransitivity(decomposedEval)
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.orTT
            elif A == TRUE and B == FALSE: return booleans.orTF
            elif A == FALSE and B == TRUE: return booleans.orFT
            elif A == FALSE and B == FALSE: return booleans.orFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'or' expression is in the set of BOOLEANS.
        '''
        leftInBool = deduceInBool(self.leftOperand)
        rightInBool = deduceInBool(self.rightOperand)
        return booleans.disjunctionClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({leftInBool, rightInBool})

Operation.registerOperation(OR, lambda operands : Or(*operands))

# if and only if: A => B and B => A
class Iff(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, IFF, A, B)
        self.A = A
        self.B = B
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return '<=>'
        elif formatType == LATEX:
            return '\Rightleftarrow'
        elif formatType == MATHML:
            return '<mo>&#x21D4;</mo>'

    def deriveLeftImplication(self):
        '''
        From (A<=>B) derive and return B=>A.
        '''
        return booleans.iffImpliesLeft.specialize({A: self.A, B: self.B}).deriveConclusion().check({self})
        
    def deriveLeft(self):
        '''
        From (A<=>B) derive and return A assuming B.
        '''
        return self.deriveLeftImplication().deriveConclusion().check({self, self.B})

    def deriveRightImplication(self):
        '''
        From (A<=>B) derive and return A=>B.
        '''
        return booleans.iffImpliesRight.specialize({A: self.A, B: self.B}).deriveConclusion().check({self})

    def deriveRight(self):
        '''
        From (A<=>B) derive and return B assuming A.
        '''
        return self.deriveRightImplication().deriveConclusion().check({self, self.A})
    
    def deriveReversed(self):
        '''
        From (A<=>B) derive and return (B<=>A).
        '''
        return booleans.iffSymmetry.specialize({A:self.A, B:self.B}).deriveConclusion().check({self})
    
    def applyTransitivity(self, otherIff):
        '''
        From A <=> B (self) and the given B <=> C (otherIff) derive and return 
        (A <=> C) assuming self and otherIff.
        Also works more generally as long as there is a common side to the equations.
        '''
        assert isinstance(otherIff, Iff)
        if self.B == otherIff.A:
            # from A <=> B, B <=> C, derive A <=> C
            compose(self, otherIff).check({self, otherIff}) # A <=> B and B <=> C
            return booleans.iffTransitivity.specialize({A:self.A, B:self.B, C:otherIff.B}).deriveConclusion().check({self, otherIff})
        elif self.A == otherIff.A:
            # from y = x and y = z, derive x = z
            return self.deriveReversed().applyTransitivity(otherIff)
        elif self.A == otherIff.B:
            # from y = x and z = y, derive x = z
            return self.deriveReversed().applyTransitivity(otherIff.deriveReversed())
        elif self.B == otherIff.B:
            # from x = y and z = y, derive x = z
            return self.applyTransitivity(otherIff.deriveReversed())
        else:
            assert False, 'transitivity cannot be applied unless there is something in common in the equalities'
        
    def definition(self):
        '''
        Return (A <=> B) = [(A => B) and (B => A)] where self represents (A <=> B).
        '''
        return booleans.iffDef.specialize({A:self.A, B:self.B}).check()
    
    def concludeViaComposition(self):
        '''
        Conclude (A <=> B) assuming both (A => B), (B => A).
        '''
        AimplB = Implies(self.A, self.B) 
        BimplA = Implies(self.B, self.A) 
        compose(AimplB, BimplA)
        return self.definition().deriveLeftViaEquivalence().check({AimplB, BimplA})
    
    def evaluate(self):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE. 
        '''
        def baseEvalFn(A, B):
            if A == TRUE and B == TRUE: return booleans.iffTT
            elif A == TRUE and B == FALSE: return booleans.iffTF
            elif A == FALSE and B == TRUE: return booleans.iffFT
            elif A == FALSE and B == FALSE: return booleans.iffFF
        return _evaluate(self, lambda : _evaluateBooleanBinaryOperation(self, baseEvalFn))

    def deduceInBool(self):
        '''
        Attempt to deduce, then return, that this 'iff' expression is in the set of BOOLEANS.
        '''
        leftInBool = deduceInBool(self.A)
        rightInBool = deduceInBool(self.B)
        return booleans.iffClosure.specialize({A:self.hypothesis, B:self.conclusion}).check({leftInBool, rightInBool})
    
    def deriveEquality(self):
        '''
        From (A <=> B), derive (A = B) assuming A and B in BOOLEANS.
        '''
        return booleans.iffOverBoolImplEq.specialize({A:self.A, B:self.B}).deriveConclusion().check({self, inBool(self.A), inBool(self.B)})

Operation.registerOperation(IFF, lambda operands : Iff(*operands))

def deriveStmtEqTrue(statement):
    '''
    For a given statement, derive statement = TRUE assuming statement.
    '''
    from equality import Equals
    return Equals(statement, TRUE).concludeBooleanEquality()

def compose(*expressions):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    print len(expressions)
    if len(expressions) == 2:
        exprA, exprB = expressions
        return booleans.conjunctionIntro.specialize({A:exprA, B:exprB}).check({exprA, exprB})
    else:
        assert len(expressions) > 2, "Compose 2 or more expressions, but not less than 2."
        rightComposition = compose(*expressions[1:])
        # A and (B and C**) = TRUE, given A, B, C**
        nestedAndEqT = deriveStmtEqTrue(compose(expressions[0], rightComposition)).check(expressions)
        # A and B and C** = A and (B and C**)
        compositionEquality = booleans.andComposition.specialize({A:expressions[0], B:rightComposition.operands[0], multiC:rightComposition.operands[1:]}).check(expressions)
        print nestedAndEqT
        print compositionEquality
        # [A and B and C**] given A, B, C**
        return compositionEquality.applyTransitivity(nestedAndEqT).deriveViaBooleanEquality().check(expressions)

def inBool(X):
    from sets import In
    return In(X, BOOLEANS)

def deduceInBool(expr):
    '''
    Attempt to deduce, then return, that the given expression is in the set of booleans.
    '''
    if hasattr(expr, 'deduceInBool'):
        return expr.deduceInBool()
    return inBool(expr)

def _evaluateBooleanBinaryOperation(operation, baseEvalFn):
    from equality import equality, f, a, b, c, x, y
    _x = operation.operand[0]
    _y = operation.operand[1]
    operator = operation.operator
    if (_x == TRUE or _x == FALSE) and (_y == TRUE or _y == FALSE):
        evaluation = baseEvalFn(_x, _y)
    elif (_x == TRUE or _x == FALSE):
        _b = _y.evaluate().rhs
        _c = baseEvalFn(_x, _b).rhs
        dummyVar = _x.safeDummyVar() # var that isn't in _x
        fOp = Operation(f, dummyVar)
        fOpSub =  Operation.make(operator, ExpressionList(_x, dummyVar))
        evaluation = equality.unaryEvaluation.specialize({fOp:fOpSub, x:_y, a:_b, c:_c}).deriveConclusion().deriveConclusion()
    elif (_y == TRUE or _y == FALSE):
        _a = _x.evaluate().rhs
        _c = baseEvalFn(_a, _y).rhs
        dummyVar = _y.safeDummyVar() # var that isn't in _y
        fOp = Operation(f, dummyVar)
        fOpSub = Operation.make(operator, ExpressionList(dummyVar, _y))
        evaluation = equality.unaryEvaluation.specialize({fOp:fOpSub, x:_x, a:_a, c:_c}).deriveConclusion().deriveConclusion()
    else:
        xEval = _x.evaluate()
        yEval = _y.evaluate()
        compose(xEval, yEval)
        _a, _b = xEval.rhs, yEval.rhs 
        _c = baseEvalFn(_a, _b).rhs
        fOp = Operation(f, (a, b))
        fOpSub = Operation.make(operator, ExpressionList(a, b))
        # f(_x, _y) = _c
        evaluation = equality.binaryEvaluation.specialize({fOp:fOpSub, x:_x, y:_y, a:_a, b:_b, c:_c}).deriveConclusion().deriveConclusion()
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


