from proveit.basiclogic.set.axioms import setOfAllDef
from proveit.basiclogic.variables import P, f, x

# forall_{P, f, x} [x in {f(y) | P(y)}] => [exists_{y | P(y)} x = f(y)]
setOfAllDef.specialize().deriveRightImplication().generalize((P, f, x)).qed(__file__)
