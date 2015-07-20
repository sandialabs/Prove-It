from proveit.basiclogic.boolean.theorems import doubleNegation, fromDoubleNegation
from proveit.basiclogic import BOOLEANS, inBool, Not, Iff
from proveit.basiclogic.variables import A

# A => Not(Not(A))
doubleNegationImplied = doubleNegation.specialize().prove()
# Not(Not(A)) => A
impliesDoubleNegation = fromDoubleNegation.specialize().prove()
# [A => Not(Not(A))] in BOOLEANS if A in BOOLEANS
doubleNegationImplied.deduceInBool().prove({inBool(A)})
# [Not(Not(A)) => A] in BOOLEANS if A in BOOLEANS
impliesDoubleNegation.deduceInBool().prove({inBool(A)})
# forall_{A} A = Not(Not(A))
Iff(A, Not(Not(A))).concludeViaComposition().deriveEquality().generalize(A, domain=BOOLEANS).qed(__file__)
