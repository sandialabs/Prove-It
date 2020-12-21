from proveit.basiclogic.set.axioms import set_of_all_def
from proveit.common import P, f, x

# forall_{P, f, x} [exists_{y | P(y)} x = f(y)] => [x in {f(y) | P(y)}]
set_of_all_def.instantiate().derive_left_implication().generalize((P, f, x)).qed(__file__)
