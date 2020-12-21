from proveit.basiclogic import Implies, Not, FALSE
from proveit.common import A

# FALSE assuming Not(A) and A
Not(A).equate_negated_to_false(
).derive_right_via_equality().proven({Not(A), A})
Implies(Not(A), Implies(A, FALSE)).generalize(A).qed(__file__)
