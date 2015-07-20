from proveit.basiclogic.boolean.theorems import falseInBool
from proveit.basiclogic import FALSE, inBool, Implies, Equals
from proveit.basiclogic.variables import A, X

# hypothesis = (FALSE=A)
hypothesis = Equals(FALSE, A)
# inBool(FALSE)
falseInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.rhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} (FALSE=A) => inBool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
