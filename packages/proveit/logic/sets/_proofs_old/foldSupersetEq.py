from proveit.basiclogic.set.axioms import superset_def
from proveit.common import A, B

# forall_{A, B} [(forall_{x in B} x in A) => (A superseteq B)]
superset_def.instantiate().derive_left_implication().generalize((A, B)).qed(__file__)
