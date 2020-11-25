from proveit.basiclogic.boolean.axioms import implicitNotF
from proveit.basiclogic import Not, Implies, Equals, FALSE, deriveStmtEqTrue
from proveit.common import A

# [Not(A) = TRUE] => [A = FALSE]
implicitNotF.instantiate().proven()
# [Not(A) = TRUE] assuming Not(A)
deriveStmtEqTrue(Not(A)).proven({Not(A)})
# forall_{A} Not(A) => [A=FALSE]
Implies(Not(A), Equals(A, FALSE)).generalize(A).qed(__file__)
