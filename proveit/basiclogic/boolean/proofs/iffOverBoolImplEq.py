from proveit.basiclogic import BOOLEANS, Forall, Iff, Implies, Equals
from proveit.common import A, B

# Note that proveByEval doesn't work for bundled Forall yet,
# but later we'll be able to do this kind of thing in one step.
# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
nestedVersion = Forall(A, Forall(B, Implies(Iff(A, B), Equals(A, B)), domain=BOOLEANS), domain=BOOLEANS).proveByEval()
# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
nestedVersion.specialize().specialize().generalize((A, B), domain=BOOLEANS).qed(__file__)
