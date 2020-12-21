from proveit.basiclogic.booleans.axioms import or_f_t, false_not_true
from proveit.basiclogic.booleans.theorems import false_eq_false
from proveit.basiclogic import FALSE, in_bool, Or, Equals, derive_stmt_eq_true
from proveit.common import X

# [FALSE or TRUE]
or_f_t.derive_via_boolean_equality().proven()
# [FALSE or FALSE=FALSE] via [FALSE or TRUE] and FALSE=FALSE
derive_stmt_eq_true(false_eq_false).sub_left_side_into(Or(FALSE, X), X).proven()
# [FALSE=TRUE or FALSE=FALSE] via [FALSE or FALSE=FALSE] and Not(FALSE=TRUE)
false_not_true.unfold().equate_negated_to_false().sub_left_side_into(Or(X, Equals(FALSE, FALSE)), X).proven()
# in_bool(FALSE) via [FALSE=TRUE or FALSE=FALSE]
in_bool(FALSE).conclude_as_folded().qed(__file__)
