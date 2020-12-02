from proveit.basiclogic.set.axioms import subsetDef
from proveit.common import A, B

# forall_{A, B} [(A subseteq B) => (forall_{x in A} x in B)]
subsetDef.instantiate().deriveRightImplication().generalize((A, B)).qed(__file__)
