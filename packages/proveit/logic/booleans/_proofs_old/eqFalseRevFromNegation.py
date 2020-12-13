from proveit.basiclogic import Implies, Not
from proveit.common import A

# Not(Not(A)) assuming A
notNotA = Not(Not(A)).concludeViaDoubleNegation()
Implies(A, notNotA.equateNegatedToFalse().deriveReversed()).generalize(A).qed(__file__)
