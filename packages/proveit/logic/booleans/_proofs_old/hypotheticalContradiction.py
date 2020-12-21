from proveit.basiclogic.booleans.axioms import contradictory_validation
from proveit.basiclogic import Implies, Not, FALSE, in_bool, BOOLEANS
from proveit.common import A

# in_bool(Not(A)) assuming in_bool(A)
Not(A).deduce_in_bool().proven({in_bool(A)})
# [Not(Not(A)) => FALSE] => Not(A) assuming in_bool(A)
contradictory_validation.instantiate({A: Not(A)}).proven({in_bool(A)})
# A assuming Not(Not(A)) and in_bool(A)
Not(Not(A)).derive_via_double_negation().proven({in_bool(A), Not(Not(A))})
# forall_{A in BOOLEANS} [A => FALSE] => Not(A)
Implies(Implies(A, FALSE), Not(A)).generalize(A, domain=BOOLEANS).qed(__file__)
