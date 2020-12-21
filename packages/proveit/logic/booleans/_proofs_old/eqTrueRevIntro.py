from proveit.basiclogic import Implies, derive_stmt_eq_true
from proveit.common import A

Implies(A, derive_stmt_eq_true(A).conclude_boolean_equality(
).derive_reversed()).generalize(A).qed(__file__)
