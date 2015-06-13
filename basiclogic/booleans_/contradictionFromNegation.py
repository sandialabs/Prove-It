from basiclogic import *

# FALSE assuming Not(A) and A
Not(A).equateNegatedToFalse().deriveRightViaEquivalence().prove({Not(A), A})
booleans.qed('contradictionFromNegation', Implies(Not(A), Implies(A, FALSE)).generalize(A))
