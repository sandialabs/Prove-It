from proveit.basiclogic import Forall, Or, Equals, TRUE, FALSE, BOOLEANS, inBool
from proveit.common import A, B

# [(A or B) = TRUE] or [(A or B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(Or(A, B), TRUE), Equals(Or(A, B), FALSE)), domain=BOOLEANS).proveByEval().instantiate().proven({inBool(A), inBool(B)})
# forall_{A in BOOLEANS} (A or  B) in BOOLEANS
inBool(Or(A, B)).concludeAsFolded().generalize((A, B), domain=BOOLEANS).qed(__file__)
