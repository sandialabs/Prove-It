from proveit.basiclogic import *

# AeqF := (A=F)
AeqF = Equals(A, FALSE)
# Not(FALSE)
booleans.notFalse
# Not(A) assuming A=FALSE because Not(FALSE)
notA = AeqF.lhsSubstitute(X, Not(X)).prove({AeqF})
booleans.qed('notFromEqFalse', Implies(AeqF, notA).generalize(A))
