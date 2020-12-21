from proveit.basiclogic.booleans.axioms import not_exists_def
from proveit.common import P, S, Qetc

not_exists_def.instantiate().left_impl_via_equivalence(
).generalize((P, Qetc, S)).qed(__file__)
