from proveit.basiclogic import Forall, Or, Not, Equals, TRUE, FALSE, BOOLEANS, inBool
from proveit.common import A

# Not(A) = TRUE or Not(A) = FALSE assuming A in BOOLEANS
Forall(A, Or(Equals(Not(A), TRUE), Equals(Not(A), FALSE)), domain=BOOLEANS).proveByEval().instantiate().proven({inBool(A)})
# forall_{A in BOOLEANS} Not(A) in BOOLEANS
inBool(Not(A)).concludeAsFolded().generalize(A, domain=BOOLEANS).qed(__file__)
