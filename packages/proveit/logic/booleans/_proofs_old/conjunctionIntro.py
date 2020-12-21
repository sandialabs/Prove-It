from proveit.basiclogic.booleans.theorems import true_and_true
from proveit.basiclogic import derive_stmt_eq_true, And, TRUE
from proveit.common import A, B, X

# A=TRUE assuming A
AeqT = derive_stmt_eq_true(A).proven({A})
# B=TRUE assuming B
BeqT = derive_stmt_eq_true(B).proven({B})
# TRUE AND TRUE
true_and_true
# (TRUE and B) assuming B via (TRUE and TRUE)
BeqT.sub_left_side_into(And(TRUE, X), X).proven({B})
# (A and B) assuming A, B via (TRUE and TRUE)
AeqT.sub_left_side_into(And(X, B), X).proven({A, B})
# forall_{A | A, B | B} (A and B)
And(A, B).generalize((A, B), conditions=(A, B)).qed(__file__)
