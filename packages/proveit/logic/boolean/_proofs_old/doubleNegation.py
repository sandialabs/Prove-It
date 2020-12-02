from proveit.basiclogic.boolean.axioms import notT
from proveit.basiclogic.boolean.theorems import notFromEqFalse
from proveit.basiclogic import Implies, Not, deriveStmtEqTrue
from proveit.common import A, X

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A)
# [Not(A)=FALSE] assuming A=TRUE
AeqT.substitution(Not(A)).applyTransitivity(notT).proven({AeqT})
# [Not(A)=FALSE] => Not(Not(A))
notFromEqFalse.instantiate({A:Not(A)}).proven()
# forall_{A} A => Not(Not(A))
Implies(A, Not(Not(A))).generalize(A).qed(__file__)
