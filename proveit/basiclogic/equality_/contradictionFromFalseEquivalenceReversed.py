from proveit.basiclogic import *

# FALSE = A
FeqA = Equals(FALSE, A)
# FALSE assumen FALSE=A and A
FeqA.deriveReversed().deriveContradiction().prove({FeqA, A})
# forall_{A} (FALSE=A) => [A => FALSE]
equality.qed('contradictionFromFalseEquivalenceReversed', Implies(FeqA, Implies(A, FALSE)).generalize([A]))
