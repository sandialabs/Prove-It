from proveit.basiclogic.boolean.theorems import trueInBool
from proveit.basiclogic import TRUE, inBool, Implies, Equals
from proveit.basiclogic.variables import A, X

# hypothesis = (A=TRUE)
hypothesis = Equals(A, TRUE)
# inBool(TRUE)
trueInBool.prove()
# inBool(A) assuming hypothesis
conclusion = hypothesis.lhsSubstitute(X, inBool(X)).prove({hypothesis})
# forall_{A} A=TRUE => inBool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
