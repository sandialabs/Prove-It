from proveit.basiclogic import BOOLEANS, Forall, Iff, Implies, Equals
from proveit.common import A, B

# Note that prove_by_eval doesn't work for bundled Forall yet,
# but later we'll be able to do this kind of thing in one step.
# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
nested_version = Forall(A, Forall(B, Implies(Iff(A, B), Equals(A, B)), domain=BOOLEANS), domain=BOOLEANS).prove_by_eval()
# forall_{A in BOOLEANS, B in BOOLEANS} (A <=> B) => (A = B)
nested_version.instantiate().instantiate().generalize((A, B), domain=BOOLEANS).qed(__file__)
