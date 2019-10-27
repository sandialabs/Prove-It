from proveit.basiclogic import Forall, And, Or, Equals, TRUE, FALSE, BOOLEANS, inBool
from proveit.common import A, B

# [(A and B) = TRUE] or [(A and B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(And(A, B), TRUE), Equals(And(A, B), FALSE)), domain=BOOLEANS).proveByEval().specialize().proven({inBool(A), inBool(B)})
# forall_{A, B in BOOLEANS} (A and B) in BOOLEANS
inBool(And(A, B)).concludeAsFolded().generalize((A, B), domain=BOOLEANS).qed(__file__)
