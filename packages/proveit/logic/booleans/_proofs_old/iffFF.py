from proveit.basiclogic.booleans.axioms import iff_def
from proveit.basiclogic.booleans.theorems import implies_f_f
from proveit.basiclogic import compose, FALSE, derive_stmt_eq_true
from proveit.common import A, B

# FALSE => FALSE
FimplF = implies_f_f.derive_via_boolean_equality()
# (FALSE => FALSE) and (FALSE => FALSE) = TRUE
FimplFandFimplF_eq_T = derive_stmt_eq_true(compose(FimplF, FimplF))
# (FALSE <=> FALSE) = TRUE
iff_def.instantiate({A: FALSE, B: FALSE}).apply_transitivity(
    FimplFandFimplF_eq_T).qed(__file__)
