from proveit.basiclogic import Implies, Not
from proveit.common import A

Implies(Not(A), Not(A).equate_negated_to_false().derive_reversed()).generalize(A).qed(__file__)
