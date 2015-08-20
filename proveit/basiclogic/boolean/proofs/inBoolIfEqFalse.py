from proveit.basiclogic.boolean.theorems import falseInBool
from proveit.basiclogic import FALSE, inBool, Implies, Equals
from proveit.common import A, X

# hypothesis = (A=FALSE)
hypothesis = Equals(A, FALSE)
# inBool(FALSE)
falseInBool.proven()
# inBool(A) assuming hypothesis
conclusion = hypothesis.lhsSubstitute(X, inBool(X)).proven({hypothesis})
# forall_{A} A=FALSE => inBool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
