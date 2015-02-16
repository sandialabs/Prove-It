from basiclogic import *

# hypothesis = [forall_{A in BOOLEANS} P(A)]
hypothesis = Forall(A, PofA, inBool(A))
# TRUE in BOOLEANS, FALSE in BOOLEANS
booleans.trueInBool, booleans.falseInBool
# P(TRUE) and P(FALSE) assuming hypothesis
conclusion = compose(hypothesis.specialize({A:TRUE}), hypothesis.specialize({A:FALSE})).prove({hypothesis})
# forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
booleans.qed('unfoldForallOverBool', Implies(hypothesis, conclusion).generalize(P))
