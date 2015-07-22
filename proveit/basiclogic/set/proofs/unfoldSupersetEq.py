from proveit.basiclogic.set.axioms import supersetDef
from proveit.basiclogic.variables import A, B

supersetDef.specialize().deriveRightImplication().generalize((A, B)).qed(__file__)
