from proveit.basiclogic.booleans.axioms import implicit_not_f
from proveit.basiclogic import Not, Implies, Equals, FALSE, derive_stmt_eq_true
from proveit.common import A

# [Not(A) = TRUE] => [A = FALSE]
implicit_not_f.instantiate().proven()
# [Not(A) = TRUE] assuming Not(A)
derive_stmt_eq_true(Not(A)).proven({Not(A)})
# forall_{A} Not(A) => [A=FALSE]
Implies(Not(A), Equals(A, FALSE)).generalize(A).qed(__file__)
