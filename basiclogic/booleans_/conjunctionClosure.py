from proveit.basiclogic import *

# [(A and B) = TRUE] or [(A and B) = FALSE] assuming A, B in BOOLEANS
Forall((A, B), Or(Equals(And(A, B), TRUE), Equals(And(A, B), FALSE)), (inBool(A), inBool(B))).proveByEval().specialize().prove({inBool(A), inBool(B)})
# forall_{A in BOOLEANS} (A and  B) in BOOLEANS
booleans.qed('conjunctionClosure', inBool(And(A, B)).concludeAsFolded().generalize((A, B), (inBool(A), inBool(B))))
