from proveit.basiclogic import Forall, Or, Equals, TRUE, FALSE, BOOLEANS, in_bool
from proveit.common import A, B

# [(A or B) = TRUE] or [(A or B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(Or(A, B), TRUE), Equals(Or(A, B), FALSE)), domain=BOOLEANS).prove_by_eval().instantiate().proven({in_bool(A), in_bool(B)})
# forall_{A in BOOLEANS} (A or  B) in BOOLEANS
in_bool(Or(A, B)).conclude_as_folded().generalize((A, B), domain=BOOLEANS).qed(__file__)
