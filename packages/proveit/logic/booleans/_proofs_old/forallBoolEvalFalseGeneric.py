from proveit.basiclogic.booleans.theorems import true_is_bool, false_is_bool
from proveit.basiclogic import Forall, Exists, Not, Implies, Equals, And, TRUE, FALSE, in_bool, BOOLEANS
from proveit.common import A, P, PofA
from proveit.basiclogic.common import PofTrue, PofFalse

# forall_{P} [(P(TRUE) = PofTrueVal) and (P(FALSE) = PofFalseVal)] =>
# {[forall_{A in BOOLEANS} P(A)] = FALSE}, assuming PofTrueVal=FALSE or
# PofFalseVal=FALSE


def forall_bool_eval_false_derivation(PofTrueVal, PofFalseVal):
    # hypothesis = [P(TRUE) = PofTrueVal] and [P(FALSE) in PofFalseVal]
    hypothesis = And(
        Equals(
            PofTrue, PofTrueVal), Equals(
            PofFalse, PofFalseVal))
    # P(TRUE) in BOOLEANS assuming hypothesis
    hypothesis.derive_left().in_bool_via_boolean_equality().proven(
        {hypothesis})
    # P(FALSE) in BOOLEANS assuming hypothesis
    hypothesis.derive_right().in_bool_via_boolean_equality().proven(
        {hypothesis})
    # forall_{A in BOOLEANS} P(A) in BOOLEANS assuming hypothesis
    Forall(
        A,
        in_bool(PofA),
        domain=BOOLEANS).conclude_as_folded().proven(
        {hypothesis})
    if PofTrueVal == FALSE:
        # Not(P(TRUE)) assuming hypothesis
        hypothesis.derive_left().derive_via_boolean_equality().proven(
            {hypothesis})
        example = TRUE
        # TRUE in BOOLEANS
        true_is_bool
    elif PofFalseVal == FALSE:
        # Not(P(FALSE)) assuming hypothesis
        hypothesis.derive_right().derive_via_boolean_equality().proven(
            {hypothesis})
        example = FALSE
        # FALSE in BOOLEANS
        false_is_bool
    # [forall_{A in BOOLEANS} P(A)] = FALSE assuming hypothesis
    conclusion = Exists(A, Not(PofA), domain=BOOLEANS).conclude_via_example(
        example).derive_negated_forall().equate_negated_to_false().proven({hypothesis})
    # forall_{P} [(P(TRUE) = FALSE) and (P(FALSE) in BOOLEANS)] => {[forall_{A
    # in BOOLEANS} P(A)] = FALSE}
    return Implies(hypothesis, conclusion).generalize(P)
