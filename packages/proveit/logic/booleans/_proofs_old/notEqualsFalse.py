from proveit.basiclogic.booleans.theorems import true_not_false
from proveit.basiclogic import FALSE, Implies, derive_stmt_eq_true, NotEquals
from proveit.common import A, X

# A=TRUE assuming A
AeqT = derive_stmt_eq_true(A)
# TRUE != FALSE
true_not_false
# (A != FALSE) assuming A
Anot_f = AeqT.sub_left_side_into(NotEquals(X, FALSE), X).proven({A})
# forall_{A} A => (A != FALSE)
Implies(A, Anot_f).generalize(A).qed(__file__)
