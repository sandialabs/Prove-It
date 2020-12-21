from proveit.basiclogic.equality.axioms import not_equals_def
from proveit.common import x, y

not_equals_def.instantiate().right_impl_via_equivalence(
).generalize((x, y)).qed(__file__)
