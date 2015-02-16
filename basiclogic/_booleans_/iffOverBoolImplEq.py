from basiclogic import *

# Note that proveByEval doesn't work for bundled Forall yet,
# but later we'll be able to do this kind of thing in one step.
# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
nestedVersion = Forall(A, Forall(B, Implies(Iff(A, B), Equals(A, B)), inBool(B)), inBool(A)).proveByEval()
# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
booleans.qed('iffOverBoolImplEq', nestedVersion.specialize().specialize().generalize((A, B), (inBool(A), inBool(B))))
