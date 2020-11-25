from proveit.basiclogic.boolean.theorems import trueInBool, falseInBool
from proveit.basiclogic import TRUE, FALSE, BOOLEANS, Implies, Forall, compose
from proveit.common import A, P, PofA

# hypothesis = [forall_{A in BOOLEANS} P(A)]
hypothesis = Forall(A, PofA, domain=BOOLEANS)
# TRUE in BOOLEANS, FALSE in BOOLEANS
trueInBool, falseInBool
# P(TRUE) and P(FALSE) assuming hypothesis
conclusion = compose(hypothesis.instantiate({A:TRUE}), hypothesis.instantiate({A:FALSE})).proven({hypothesis})
# forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
Implies(hypothesis, conclusion).generalize(P).qed(__file__)
