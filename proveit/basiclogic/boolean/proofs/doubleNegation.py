from proveit.basiclogic.boolean.axioms import notT
from proveit.basiclogic.boolean.theorems import notFromEqFalse
from proveit.basiclogic import Implies, Not, deriveStmtEqTrue
from proveit.basiclogic.variables import A, X

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A)
# [Not(A)=FALSE] assuming A=TRUE
AeqT.substitution(X, Not(X)).applyTransitivity(notT).prove({AeqT})
# [Not(A)=FALSE] => Not(Not(A))
notFromEqFalse.specialize({A:Not(A)}).prove()
# forall_{A} A => Not(Not(A))
Implies(A, Not(Not(A))).generalize(A).qed(__file__)
