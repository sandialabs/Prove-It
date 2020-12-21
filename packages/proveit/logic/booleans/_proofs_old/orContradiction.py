from proveit.basiclogic.booleans.theorems import not_or_from_neither
from proveit.basiclogic import Not
from proveit.common import A, B

# (A or B) => FALSE assuming Not(A), Not(B)
AorB_impl_F = not_or_from_neither.instantiate().derive_conclusion().derive_conclusion().derive_contradiction().derive_conclusion()
AorB_impl_F.generalize((A, B), conditions=(Not(A), Not(B))).qed(__file__)
