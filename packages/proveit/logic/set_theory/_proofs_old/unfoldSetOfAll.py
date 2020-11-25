from proveit.basiclogic.set.axioms import setOfAllDef
from proveit.common import P, f, x

# forall_{P, f, x} [x in {f(y) | P(y)}] => [exists_{y | P(y)} x = f(y)]
setOfAllDef.instantiate().deriveRightImplication().generalize((P, f, x)).qed(__file__)
