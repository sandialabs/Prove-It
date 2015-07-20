from proveit.basiclogic.boolean.theorems import falseInBool
from proveit.basiclogic import FALSE, inBool, Implies, Equals
from proveit.basiclogic.variables import A, X

# hypothesis = (A=FALSE)
hypothesis = Equals(A, FALSE)
# inBool(FALSE)
falseInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.lhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} A=FALSE => inBool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
