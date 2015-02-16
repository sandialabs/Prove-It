from basiclogic import *

booleans.qed('notImpliesEqFalseRev', Implies(Not(A), Not(A).equateNegatedToFalse().deriveReversed()).generalize(A))
