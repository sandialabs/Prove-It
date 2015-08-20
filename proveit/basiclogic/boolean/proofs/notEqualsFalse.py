from proveit.basiclogic.boolean.theorems import trueNotFalse
from proveit.basiclogic import FALSE, Implies, deriveStmtEqTrue, NotEquals
from proveit.common import A, X

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A)
# TRUE != FALSE
trueNotFalse
# (A != FALSE) assuming A
AnotF = AeqT.lhsSubstitute(X, NotEquals(X, FALSE)).proven({A})
# forall_{A} A => (A != FALSE)
Implies(A, AnotF).generalize(A).qed(__file__)
