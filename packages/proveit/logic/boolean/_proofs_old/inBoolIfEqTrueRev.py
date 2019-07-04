from proveit.basiclogic.boolean.theorems import trueInBool
from proveit.basiclogic import TRUE, inBool, Implies, Equals
from proveit.common import A, X

# hypothesis = (TRUE=A)
hypothesis = Equals(TRUE, A)
# inBool(TRUE)
trueInBool.proven()
# inBool(A) assuming hypothesis
conclusion = hypothesis.subRightSideInto(inBool(X), X).proven({hypothesis})
# forall_{A} (TRUE=A) => inBool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
