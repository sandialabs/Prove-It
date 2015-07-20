from proveit.basiclogic.boolean.axioms import contradictoryValidation
from proveit.basiclogic import Implies, Not, FALSE, inBool
from proveit.basiclogic.variables import A

# inBool(Not(A)) assuming inBool(A)
Not(A).deduceInBool().prove({inBool(A)})
# [Not(Not(A)) => FALSE] => Not(A) assuming inBool(A)
contradictoryValidation.specialize({A:Not(A)}).prove({inBool(A)})
# A assuming Not(Not(A)) and inBool(A)
Not(Not(A)).deriveViaDoubleNegation().prove({inBool(A), Not(Not(A))})
# forall_{A in BOOLEANS} [A => FALSE] => Not(A)
Implies(Implies(A, FALSE), Not(A)).generalize(A, inBool(A)).qed(__file__)
