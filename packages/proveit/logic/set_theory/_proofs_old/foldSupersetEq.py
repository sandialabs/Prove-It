from proveit.basiclogic.set.axioms import supersetDef
from proveit.common import A, B

# forall_{A, B} [(forall_{x in B} x in A) => (A superseteq B)]
supersetDef.instantiate().deriveLeftImplication().generalize((A, B)).qed(__file__)
