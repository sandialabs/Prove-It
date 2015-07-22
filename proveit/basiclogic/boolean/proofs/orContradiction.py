from proveit.basiclogic.boolean.theorems import notOrFromNeither
from proveit.basiclogic import Not
from proveit.basiclogic.variables import A, B

# (A or B) => FALSE assuming Not(A), Not(B)
AorB_impl_F = notOrFromNeither.specialize().deriveConclusion().deriveConclusion().deriveContradiction().deriveConclusion()
AorB_impl_F.generalize((A, B), conditions=(Not(A), Not(B))).qed(__file__)
