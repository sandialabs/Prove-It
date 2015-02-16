from basiclogic import *

# [Not(A) = TRUE] => [A = FALSE]
booleans.implicitNotF.specialize().prove()
# [Not(A) = TRUE] assuming Not(A)
deriveStmtEqTrue(Not(A)).prove({Not(A)})
# forall_{A} Not(A) => [A=FALSE]
booleans.qed('notImpliesEqFalse', Implies(Not(A), Equals(A, FALSE)).generalize(A))
