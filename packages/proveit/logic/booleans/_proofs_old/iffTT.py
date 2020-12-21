from proveit.basiclogic.booleans.axioms import iff_def
from proveit.basiclogic.booleans.theorems import implies_t_t
from proveit.basiclogic import compose, TRUE, derive_stmt_eq_true
from proveit.common import A, B

# TRUE => TRUE
TimplT = implies_t_t.derive_via_boolean_equality()
# (TRUE => TRUE) and (TRUE => TRUE) = TRUE
TimplTandTimplT_eq_T = derive_stmt_eq_true(compose(TimplT, TimplT))
# (TRUE <=> TRUE) = TRUE
iff_def.instantiate({A: TRUE, B: TRUE}).apply_transitivity(
    TimplTandTimplT_eq_T).qed(__file__)
