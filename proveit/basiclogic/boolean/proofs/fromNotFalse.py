from proveit.basiclogic import Implies, BOOLEANS, FALSE, inBool, compose, NotEquals
from proveit.common import A

# AnotF = (A != FALSE)
AnotF = NotEquals(A, FALSE)
# notAeqF = Not(A = FALSE)
notAeqF = AnotF.unfold()
# (A=TRUE or A=FALSE) assuming inBool(A)
AeqT_or_AeqF = inBool(A).unfold()
AeqT = AeqT_or_AeqF.operands[0]
# Not(A=FALSE) and (A=TRUE or A=FALSE) assuming each
compose(notAeqF, AeqT_or_AeqF).proven({AnotF, AeqT_or_AeqF})
# inBool(A=TRUE)
AeqT.deduceInBool()
# A assuming inBool(A), Not(A=FALSE)
AeqT_or_AeqF.deriveLeftIfNotRight().deriveViaBooleanEquality().proven({inBool(A), AnotF})
# forall_{A in BOOLEANS} Not(A=FALSE) => A
Implies(AnotF, A).generalize(A, domain=BOOLEANS).qed(__file__)
