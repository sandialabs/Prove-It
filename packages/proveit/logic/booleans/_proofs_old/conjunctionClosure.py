from proveit.basiclogic import Forall, And, Or, Equals, TRUE, FALSE, BOOLEANS, in_bool
from proveit.common import A, B

# [(A and B) = TRUE] or [(A and B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(And(A, B), TRUE), Equals(And(A, B), FALSE)), domain=BOOLEANS).prove_by_eval().instantiate().proven({in_bool(A), in_bool(B)})
# forall_{A, B in BOOLEANS} (A and B) in BOOLEANS
in_bool(And(A, B)).conclude_as_folded().generalize((A, B), domain=BOOLEANS).qed(__file__)
