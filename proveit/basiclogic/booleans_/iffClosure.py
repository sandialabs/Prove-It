from proveit.basiclogic import *

# [(A<=>B) = TRUE] or [(A<=>B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(Iff(A, B), TRUE), Equals(Iff(A, B), FALSE)), (inBool(A), inBool(B))).proveByEval().specialize().prove({inBool(A), inBool(B)})
# forall_{A in BOOLEANS} (A <=> B) in BOOLEANS
booleans.qed('iffClosure', inBool(Iff(A, B)).concludeAsFolded().generalize((A, B), (inBool(A), inBool(B))))
