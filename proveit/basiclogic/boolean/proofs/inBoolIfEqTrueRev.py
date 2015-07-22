from proveit.basiclogic.boolean.theorems import trueInBool
from proveit.basiclogic import TRUE, inBool, Implies, Equals
from proveit.common import A, X

# hypothesis = (TRUE=A)
hypothesis = Equals(TRUE, A)
# inBool(TRUE)
trueInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.rhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} (TRUE=A) => inBool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
