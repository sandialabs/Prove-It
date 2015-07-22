from proveit.basiclogic import Forall, Implies, Or, Equals, TRUE, FALSE, BOOLEANS, inBool
from proveit.common import A, B

# [(A=>B) = TRUE] or [(A=>B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(Implies(A, B), TRUE), Equals(Implies(A, B), FALSE)), domain=BOOLEANS).proveByEval().specialize().prove({inBool(A), inBool(B)})
# forall_{A in BOOLEANS} (A => B) in BOOLEANS
inBool(Implies(A, B)).concludeAsFolded().generalize((A, B), domain=BOOLEANS).qed(__file__)
