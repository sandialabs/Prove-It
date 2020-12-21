from proveit.basiclogic.set.axioms import subset_def
from proveit.common import A, B

# forall_{A, B} [(A subseteq B) => (forall_{x in A} x in B)]
subset_def.instantiate().derive_right_implication().generalize((A, B)).qed(__file__)
