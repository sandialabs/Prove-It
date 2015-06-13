from basiclogic import *

booleans.qed('impliesTT', deriveStmtEqTrue(booleans.trueConclusion.specialize({A:TRUE})))
