from proveit.basiclogic.boolean.theorems import trueNotFalse
from proveit.basiclogic import FALSE, Implies, deriveStmtEqTrue, NotEquals
from proveit.common import A, X

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A)
# TRUE != FALSE
trueNotFalse
# (A != FALSE) assuming A
AnotF = AeqT.lhsSubstitute(NotEquals(X, FALSE), X).proven({A})
# forall_{A} A => (A != FALSE)
Implies(A, AnotF).generalize(A).qed(__file__)
