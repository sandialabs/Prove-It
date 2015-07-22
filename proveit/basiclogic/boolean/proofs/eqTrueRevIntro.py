from proveit.basiclogic import Implies, deriveStmtEqTrue
from proveit.common import A

Implies(A, deriveStmtEqTrue(A).concludeBooleanEquality().deriveReversed()).generalize(A).qed(__file__)
