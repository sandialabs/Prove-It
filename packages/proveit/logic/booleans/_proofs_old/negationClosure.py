from proveit.basiclogic import Forall, Or, Not, Equals, TRUE, FALSE, BOOLEANS, in_bool
from proveit.common import A

# Not(A) = TRUE or Not(A) = FALSE assuming A in BOOLEANS
Forall(A, Or(Equals(Not(A), TRUE), Equals(Not(A), FALSE)),
       domain=BOOLEANS).prove_by_eval().instantiate().proven({in_bool(A)})
# forall_{A in BOOLEANS} Not(A) in BOOLEANS
in_bool(Not(A)).conclude_as_folded().generalize(
    A, domain=BOOLEANS).qed(__file__)
