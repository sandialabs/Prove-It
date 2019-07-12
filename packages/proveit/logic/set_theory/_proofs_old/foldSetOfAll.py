from proveit.basiclogic.set.axioms import setOfAllDef
from proveit.common import P, f, x

# forall_{P, f, x} [exists_{y | P(y)} x = f(y)] => [x in {f(y) | P(y)}]
setOfAllDef.specialize().deriveLeftImplication().generalize((P, f, x)).qed(__file__)
