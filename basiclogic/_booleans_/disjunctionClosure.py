from basiclogic import *

# [(A or B) = TRUE] or [(A or B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(Or(A, B), TRUE), Equals(Or(A, B), FALSE)), (inBool(A), inBool(B))).proveByEval().specialize().prove({inBool(A), inBool(B)})
# forall_{A in BOOLEANS} (A or  B) in BOOLEANS
booleans.qed('disjunctionClosure', inBool(Or(A, B)).concludeAsFolded().generalize((A, B), (inBool(A), inBool(B))))
