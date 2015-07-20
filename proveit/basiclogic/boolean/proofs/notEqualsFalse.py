from proveit.basiclogic.boolean.theorems import trueNotFalse
from proveit.basiclogic import FALSE, Implies, deriveStmtEqTrue, NotEquals
from proveit.basiclogic.variables import A, X

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A)
# TRUE != FALSE
trueNotFalse
# (A != FALSE) assuming A
AnotF = AeqT.lhsSubstitute(X, NotEquals(X, FALSE)).prove({A})
# forall_{A} A => (A != FALSE)
Implies(A, AnotF).generalize(A).qed(__file__)
