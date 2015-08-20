from proveit.basiclogic.boolean.axioms import contradictoryValidation
from proveit.basiclogic import Implies, Not, FALSE, inBool, BOOLEANS
from proveit.common import A

# inBool(Not(A)) assuming inBool(A)
Not(A).deduceInBool().proven({inBool(A)})
# [Not(Not(A)) => FALSE] => Not(A) assuming inBool(A)
contradictoryValidation.specialize({A:Not(A)}).proven({inBool(A)})
# A assuming Not(Not(A)) and inBool(A)
Not(Not(A)).deriveViaDoubleNegation().proven({inBool(A), Not(Not(A))})
# forall_{A in BOOLEANS} [A => FALSE] => Not(A)
Implies(Implies(A, FALSE), Not(A)).generalize(A, domain=BOOLEANS).qed(__file__)
