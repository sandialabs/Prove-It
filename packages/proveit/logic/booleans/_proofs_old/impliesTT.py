from proveit.basiclogic.booleans.theorems import true_conclusion
from proveit.basiclogic import derive_stmt_eq_true, TRUE
from proveit.common import A

derive_stmt_eq_true(true_conclusion.instantiate({A: TRUE})).qed(__file__)
