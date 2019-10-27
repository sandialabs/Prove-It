from proveit.basiclogic.set.theorems import unfoldSetOfAll
from proveit.common import y, fy

# forall_{P, x} [x in {y | P(y)}] => [exists_{y | P(y)} x = y]
unfoldSetOfAll.specialize({fy:y})
