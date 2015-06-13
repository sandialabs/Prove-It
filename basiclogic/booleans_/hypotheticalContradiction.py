from proveit.basiclogic import *

# inBool(Not(A)) assuming inBool(A)
Not(A).deduceInBool().prove({inBool(A)})
# [Not(Not(A)) => FALSE] => Not(A) assuming inBool(A)
booleans.contradictoryValidation.specialize({A:Not(A)}).prove({inBool(A)})
# A assuming Not(Not(A)) and inBool(A)
Not(Not(A)).deriveViaDoubleNegation().prove({inBool(A), Not(Not(A))})
# forall_{A in BOOLEANS} [A => FALSE] => Not(A)
booleans.qed('hypotheticalContradiction', Implies(Implies(A, FALSE), Not(A)).generalize(A, inBool(A)))
