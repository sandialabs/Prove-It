from proveit.basiclogic import FALSE, Equals, Implies
from proveit.common import A

# A = FALSE
AeqF = Equals(A, FALSE)
# FALSE assuming A=FALSE and A
AeqF.deriveRightViaEquivalence().proven({AeqF, A})
# forall_{A} (A=FALSE) => [A => FALSE]
Implies(AeqF, Implies(A, FALSE)).generalize([A]).qed(__file__)
