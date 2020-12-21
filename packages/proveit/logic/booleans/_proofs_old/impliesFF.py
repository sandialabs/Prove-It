from proveit.basiclogic.booleans.theorems import self_implication
from proveit.basiclogic import derive_stmt_eq_true, FALSE
from proveit.common import A

derive_stmt_eq_true(self_implication.instantiate({A:FALSE})).qed(__file__)
