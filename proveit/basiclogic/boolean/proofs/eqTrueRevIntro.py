from proveit.basiclogic import Implies, deriveStmtEqTrue
from proveit.basiclogic.variables import A

Implies(A, deriveStmtEqTrue(A).concludeBooleanEquality().deriveReversed()).generalize(A).qed(__file__)
