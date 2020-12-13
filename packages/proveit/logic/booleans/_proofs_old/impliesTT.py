from proveit.basiclogic.booleans.theorems import trueConclusion
from proveit.basiclogic import deriveStmtEqTrue, TRUE
from proveit.common import A

deriveStmtEqTrue(trueConclusion.instantiate({A:TRUE})).qed(__file__)
