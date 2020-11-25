from proveit.basiclogic.boolean.theorems import trueConclusion
from proveit.basiclogic import deriveStmtEqTrue, FALSE
from proveit.common import A

deriveStmtEqTrue(trueConclusion.instantiate({A:FALSE})).qed(__file__)
