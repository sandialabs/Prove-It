from proveit.basiclogic.set.theorems import unfold_set_of_all
from proveit.common import y, fy

# forall_{P, x} [x in {y | P(y)}] => [exists_{y | P(y)} x = y]
unfold_set_of_all.instantiate({fy:y})
