from basiclogic import *

booleans.qed('eqTrueRevIntro', Implies(A, deriveStmtEqTrue(A).concludeBooleanEquality().deriveReversed()).generalize(A))
