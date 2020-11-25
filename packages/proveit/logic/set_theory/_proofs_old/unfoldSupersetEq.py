from proveit.basiclogic.set.axioms import supersetDef
from proveit.common import A, B

supersetDef.instantiate().deriveRightImplication().generalize((A, B)).qed(__file__)
