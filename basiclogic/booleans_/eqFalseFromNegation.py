from proveit.basiclogic import *

# Not(Not(A)) assuming A
notNotA = Not(Not(A)).concludeViaDoubleNegation()
booleans.qed('eqFalseFromNegation', Implies(A, notNotA.equateNegatedToFalse()).generalize(A))
