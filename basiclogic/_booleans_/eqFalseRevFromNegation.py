from basiclogic import *

# Not(Not(A)) assuming A
notNotA = Not(Not(A)).concludeViaDoubleNegation()
booleans.qed('eqFalseRevFromNegation', Implies(A, notNotA.equateNegatedToFalse().deriveReversed()).generalize(A))
