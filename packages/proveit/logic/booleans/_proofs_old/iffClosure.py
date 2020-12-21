from proveit.basiclogic import Forall, Iff, Or, Equals, TRUE, FALSE, BOOLEANS, in_bool
from proveit.common import A, B

# [(A<=>B) = TRUE] or [(A<=>B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(Iff(A, B), TRUE), Equals(Iff(A, B), FALSE)),
       domain=BOOLEANS).prove_by_eval().instantiate().proven({in_bool(A), in_bool(B)})
# forall_{A in BOOLEANS} (A <=> B) in BOOLEANS
in_bool(Iff(A, B)).conclude_as_folded().generalize(
    (A, B), domain=BOOLEANS).qed(__file__)
