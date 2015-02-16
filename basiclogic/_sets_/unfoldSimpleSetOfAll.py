from basiclogic import *

# forall_{P, x} [x in {y | P(y)}] => [exists_{y | P(y)} x = y]
sets.unfoldSetOfAll.specialize({f:Lambda([y], y)})
