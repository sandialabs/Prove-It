from proveit.basiclogic import *

# A = FALSE
AeqF = Equals(A, FALSE)
# FALSE assuming A=FALSE and A
AeqF.deriveRightViaEquivalence().prove({AeqF, A})
# forall_{A} (A=FALSE) => [A => FALSE]
equality.qed('contradictionFromFalseEquivalence', Implies(AeqF, Implies(A, FALSE)).generalize([A]))
