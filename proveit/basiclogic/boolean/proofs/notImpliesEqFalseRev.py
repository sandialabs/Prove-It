from proveit.basiclogic import Implies, Not
from proveit.common import A

Implies(Not(A), Not(A).equateNegatedToFalse().deriveReversed()).generalize(A).qed(__file__)
