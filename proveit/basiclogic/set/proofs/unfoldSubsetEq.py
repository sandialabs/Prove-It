from proveit.basiclogic.set.axioms import subsetDef
from proveit.basiclogic.variables import A, B

# forall_{A, B} [(A subseteq B) => (forall_{x in A} x in B)]
subsetDef.specialize().deriveRightImplication().generalize((A, B)).qed(__file__)
