from proveit.basiclogic.boolean.theorems import selfImplication
from proveit.basiclogic import deriveStmtEqTrue, FALSE
from proveit.common import A

deriveStmtEqTrue(selfImplication.specialize({A:FALSE})).qed(__file__)
