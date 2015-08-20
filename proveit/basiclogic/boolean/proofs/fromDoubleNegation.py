from proveit.basiclogic.boolean.axioms import implicitNotF, implicitNotT
from proveit.basiclogic import Implies, Not, deriveStmtEqTrue
from proveit.common import A

# hypothesis: Not(Not(A))
hypothesis = Not(Not(A))
# [Not(Not(A)) = TRUE] assuming hypothesis
deriveStmtEqTrue(hypothesis).proven({hypothesis})
# [Not(A) = FALSE] assuming hypothesis
implicitNotF.specialize({A:Not(A)}).deriveConclusion().proven({hypothesis})
# A assuming hypothesis
implicitNotT.specialize().deriveConclusion().deriveViaBooleanEquality().proven({hypothesis})
# forall_{A} Not(Not(A)) => A
Implies(Not(Not(A)), A).generalize(A).qed(__file__)
