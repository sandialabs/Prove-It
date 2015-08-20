from proveit.basiclogic.boolean.theorems import doubleNegation, fromDoubleNegation
from proveit.basiclogic import BOOLEANS, inBool, Not, Iff
from proveit.common import A

# A => Not(Not(A))
doubleNegationImplied = doubleNegation.specialize().proven()
# Not(Not(A)) => A
impliesDoubleNegation = fromDoubleNegation.specialize().proven()
# [A => Not(Not(A))] in BOOLEANS if A in BOOLEANS
doubleNegationImplied.deduceInBool().proven({inBool(A)})
# [Not(Not(A)) => A] in BOOLEANS if A in BOOLEANS
impliesDoubleNegation.deduceInBool().proven({inBool(A)})
# forall_{A} A = Not(Not(A))
Iff(A, Not(Not(A))).concludeViaComposition().deriveEquality().generalize(A, domain=BOOLEANS).qed(__file__)
