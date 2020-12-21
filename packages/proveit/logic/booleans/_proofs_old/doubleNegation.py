from proveit.basiclogic.booleans.axioms import not_t
from proveit.basiclogic.booleans.theorems import not_from_eq_false
from proveit.basiclogic import Implies, Not, derive_stmt_eq_true
from proveit.common import A, X

# A=TRUE assuming A
AeqT = derive_stmt_eq_true(A)
# [Not(A)=FALSE] assuming A=TRUE
AeqT.substitution(Not(A)).apply_transitivity(not_t).proven({AeqT})
# [Not(A)=FALSE] => Not(Not(A))
not_from_eq_false.instantiate({A:Not(A)}).proven()
# forall_{A} A => Not(Not(A))
Implies(A, Not(Not(A))).generalize(A).qed(__file__)
