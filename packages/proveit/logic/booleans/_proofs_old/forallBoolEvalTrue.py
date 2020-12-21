from proveit.basiclogic.booleans.theorems import fold_forall_over_bool
from proveit.basiclogic import Implies, derive_stmt_eq_true
from proveit.common import P

# P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
folding = fold_forall_over_bool.instantiate()
# forall_{P} [P(TRUE) and P(FALSE)] => {[forall_{A in BOOLEANS} P(A)] = TRUE}
Implies(folding.hypothesis, derive_stmt_eq_true(folding.derive_conclusion())).generalize(P).qed(__file__)
