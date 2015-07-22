from proveit.basiclogic.set.theorems import unfoldSetOfAll
from proveit.basiclogic.variables import y
from proveit.basiclogic.simpleExpr import fy

# forall_{P, x} [x in {y | P(y)}] => [exists_{y | P(y)} x = y]
unfoldSetOfAll.specialize({fy:y})
