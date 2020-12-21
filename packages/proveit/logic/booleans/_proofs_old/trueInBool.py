from proveit.basiclogic.booleans.axioms import or_t_f
from proveit.basiclogic.booleans.theorems import true_not_false, true_eq_true
from proveit.basiclogic import TRUE, FALSE, in_bool, Or, Equals, derive_stmt_eq_true
from proveit.common import X

# [TRUE or FALSE]
or_t_f.derive_via_boolean_equality().proven()
# [TRUE or TRUE=FALSE] via [TRUE or FALSE] and TRUE != FALSE
true_not_false.unfold().equate_negated_to_false().sub_left_side_into(Or(TRUE, X), X).proven()
# [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
derive_stmt_eq_true(true_eq_true).sub_left_side_into(Or(X, Equals(TRUE, FALSE)), X).proven()
# in_bool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
in_bool(TRUE).conclude_as_folded().qed(__file__)
