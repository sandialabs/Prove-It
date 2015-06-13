from proveit.basiclogic import *

# AnotF = (A != FALSE)
AnotF = NotEquals(A, FALSE)
# notAeqF = Not(A = FALSE)
notAeqF = AnotF.unfold()
# (A=TRUE or A=FALSE) assuming inBool(A)
AeqT_or_AeqF = inBool(A).unfold()
AeqT = AeqT_or_AeqF.operands[0]
# Not(A=FALSE) and (A=TRUE or A=FALSE) assuming each
compose(notAeqF, AeqT_or_AeqF).prove({AnotF, AeqT_or_AeqF})
# inBool(A=TRUE)
AeqT.deduceInBool()
# A assuming inBool(A), Not(A=FALSE)
AeqT_or_AeqF.deriveLeftIfNotRight().deriveViaBooleanEquality().prove({inBool(A), AnotF})
# forall_{A | inBool(A)} Not(A=FALSE) => A
booleans.qed('fromNotFalse', Implies(AnotF, A).generalize(A, inBool(A)))
