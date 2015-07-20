from proveit.basiclogic.boolean.theorems import trueInBool, falseInBool
from proveit.basiclogic import TRUE, FALSE, BOOLEANS, Implies, Forall, compose
from proveit.basiclogic.variables import A, P
from proveit.basiclogic.simpleExpr import PofA

# hypothesis = [forall_{A in BOOLEANS} P(A)]
hypothesis = Forall(A, PofA, domain=BOOLEANS)
# TRUE in BOOLEANS, FALSE in BOOLEANS
trueInBool, falseInBool
# P(TRUE) and P(FALSE) assuming hypothesis
conclusion = compose(hypothesis.specialize({A:TRUE}), hypothesis.specialize({A:FALSE})).prove({hypothesis})
# forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
Implies(hypothesis, conclusion).generalize(P).qed(__file__)
