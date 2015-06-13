from proveit.basiclogic import *

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A)
# TRUE != FALSE
booleans.trueNotFalse
# (A != FALSE) assuming A
AnotF = AeqT.lhsSubstitute(X, NotEquals(X, FALSE)).prove({A})
# forall_{A} A => (A != FALSE)
booleans.qed('notEqualsFalse', Implies(A, AnotF).generalize(A))
