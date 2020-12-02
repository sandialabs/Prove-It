from proveit.basiclogic.set.axioms import subsetDef
from proveit.common import A, B

# forall_{A, B} [(forall_{x in A} x in B) => (A subseteq B)]
subsetDef.instantiate().deriveLeftImplication().generalize((A, B)).qed(__file__)
