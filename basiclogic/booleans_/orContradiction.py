from basiclogic import *

# (A or B) => FALSE assuming Not(A), Not(B)
AorB_impl_F = booleans.notOrFromNeither.specialize().deriveConclusion().deriveConclusion().deriveContradiction().deriveConclusion()
booleans.qed('orContradiction', AorB_impl_F.generalize((A, B), (Not(A), Not(B))))
