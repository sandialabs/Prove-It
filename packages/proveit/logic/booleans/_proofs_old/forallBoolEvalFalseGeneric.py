from proveit.basiclogic.booleans.theorems import trueInBool, falseInBool
from proveit.basiclogic import Forall, Exists, Not, Implies, Equals, And, TRUE, FALSE, inBool, BOOLEANS
from proveit.common import A, P, PofA
from proveit.basiclogic.common import PofTrue, PofFalse

# forall_{P} [(P(TRUE) = PofTrueVal) and (P(FALSE) = PofFalseVal)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}, assuming PofTrueVal=FALSE or PofFalseVal=FALSE
def forallBoolEvalFalseDerivation(PofTrueVal, PofFalseVal):
    # hypothesis = [P(TRUE) = PofTrueVal] and [P(FALSE) in PofFalseVal]
    hypothesis = And(Equals(PofTrue, PofTrueVal), Equals(PofFalse, PofFalseVal))
    # P(TRUE) in BOOLEANS assuming hypothesis
    hypothesis.deriveLeft().inBoolViaBooleanEquality().proven({hypothesis})
    # P(FALSE) in BOOLEANS assuming hypothesis
    hypothesis.deriveRight().inBoolViaBooleanEquality().proven({hypothesis})
    # forall_{A in BOOLEANS} P(A) in BOOLEANS assuming hypothesis
    Forall(A, inBool(PofA), domain=BOOLEANS).concludeAsFolded().proven({hypothesis})
    if PofTrueVal == FALSE:
        # Not(P(TRUE)) assuming hypothesis
        hypothesis.deriveLeft().deriveViaBooleanEquality().proven({hypothesis})
        example = TRUE
        # TRUE in BOOLEANS
        trueInBool
    elif PofFalseVal == FALSE:
        # Not(P(FALSE)) assuming hypothesis
        hypothesis.deriveRight().deriveViaBooleanEquality().proven({hypothesis})
        example = FALSE    
        # FALSE in BOOLEANS
        falseInBool
    # [forall_{A in BOOLEANS} P(A)] = FALSE assuming hypothesis
    conclusion = Exists(A, Not(PofA), domain=BOOLEANS).concludeViaExample(example).deriveNegatedForall().equateNegatedToFalse().proven({hypothesis})
    # forall_{P} [(P(TRUE) = FALSE) and (P(FALSE) in BOOLEANS)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}
    return Implies(hypothesis, conclusion).generalize(P)
