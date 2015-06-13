from basiclogic import *

# hypothesis: Not(Not(A))
hypothesis = Not(Not(A))
# [Not(Not(A)) = TRUE] assuming hypothesis
deriveStmtEqTrue(hypothesis).prove({hypothesis})
# [Not(A) = FALSE] assuming hypothesis
booleans.implicitNotF.specialize({A:Not(A)}).deriveConclusion().prove({hypothesis})
# A assuming hypothesis
booleans.implicitNotT.specialize().deriveConclusion().deriveViaBooleanEquality().prove({hypothesis})
# forall_{A} Not(Not(A)) => A
booleans.qed('fromDoubleNegation', Implies(Not(Not(A)), A).generalize(A))
