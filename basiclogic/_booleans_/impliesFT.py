from basiclogic import *

booleans.qed('impliesFT', deriveStmtEqTrue(booleans.trueConclusion.specialize({A:FALSE})))
