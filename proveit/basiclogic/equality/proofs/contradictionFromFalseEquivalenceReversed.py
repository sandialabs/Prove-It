from proveit.basiclogic import FALSE, Equals, Implies
from proveit.common import A

# FALSE = A
FeqA = Equals(FALSE, A)
# FALSE assumen FALSE=A and A
FeqA.deriveReversed().deriveContradiction().proven({FeqA, A})
# forall_{A} (FALSE=A) => [A => FALSE]
Implies(FeqA, Implies(A, FALSE)).generalize([A]).qed(__file__)
