from proveit.basiclogic import Implies, Not
from proveit.common import A

# Not(Not(A)) assuming A
not_not_a = Not(Not(A)).conclude_via_double_negation()
Implies(A, not_not_a.equate_negated_to_false().derive_reversed()).generalize(A).qed(__file__)
