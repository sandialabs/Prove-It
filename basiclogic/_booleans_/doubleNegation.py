from basiclogic import *

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A)
# [Not(A)=FALSE] assuming A=TRUE
AeqT.substitution(X, Not(X)).applyTransitivity(booleans.notT).prove({AeqT})
# [Not(A)=FALSE] => Not(Not(A))
booleans.notFromEqFalse.specialize({A:Not(A)}).prove()
# forall_{A} A => Not(Not(A))
booleans.qed('doubleNegation', Implies(A, Not(Not(A))).generalize(A))
