from basiclogic import *

# Not(A) = TRUE or Not(A) = FALSE assuming A in BOOLEANS
Forall(A, Or(Equals(Not(A), TRUE), Equals(Not(A), FALSE)), inBool(A)).proveByEval().specialize().prove({inBool(A)})
# forall_{A in BOOLEANS} Not(A) in BOOLEANS
booleans.qed('negationClosure', inBool(Not(A)).concludeAsFolded().generalize(A, inBool(A)))
