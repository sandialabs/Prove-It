from proveit.basiclogic.booleans.theorems import selfImplication
from proveit.basiclogic import deriveStmtEqTrue, FALSE
from proveit.common import A

deriveStmtEqTrue(selfImplication.instantiate({A:FALSE})).qed(__file__)
