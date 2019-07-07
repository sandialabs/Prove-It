from proveit.basiclogic import Forall, Iff, Or, Equals, TRUE, FALSE, BOOLEANS, inBool
from proveit.common import A, B

# [(A<=>B) = TRUE] or [(A<=>B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(Iff(A, B), TRUE), Equals(Iff(A, B), FALSE)), domain=BOOLEANS).proveByEval().specialize().proven({inBool(A), inBool(B)})
# forall_{A in BOOLEANS} (A <=> B) in BOOLEANS
inBool(Iff(A, B)).concludeAsFolded().generalize((A, B), domain=BOOLEANS).qed(__file__)
