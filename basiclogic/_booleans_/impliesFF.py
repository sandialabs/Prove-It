from basiclogic import *

booleans.qed('impliesFF', deriveStmtEqTrue(booleans.selfImplication.specialize({A:FALSE})))
