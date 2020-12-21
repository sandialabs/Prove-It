from proveit.basiclogic.set.axioms import set_of_all_def
from proveit.common import P, f, x

# forall_{P, f, x} [x in {f(y) | P(y)}] => [exists_{y | P(y)} x = f(y)]
set_of_all_def.instantiate().derive_right_implication(
).generalize((P, f, x)).qed(__file__)
