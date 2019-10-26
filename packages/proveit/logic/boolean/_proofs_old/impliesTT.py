from proveit.basiclogic.boolean.theorems import trueConclusion
from proveit.basiclogic import deriveStmtEqTrue, TRUE
from proveit.common import A

deriveStmtEqTrue(trueConclusion.specialize({A:TRUE})).qed(__file__)
