from proveit.basiclogic.set.axioms import subset_def
from proveit.common import A, B

# forall_{A, B} [(forall_{x in A} x in B) => (A subseteq B)]
subset_def.instantiate().derive_left_implication().generalize((A, B)).qed(__file__)
