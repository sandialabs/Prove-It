from proveit.basiclogic.boolean.axioms import implicitNotF, implicitNotT
from proveit.basiclogic import Implies, Not, deriveStmtEqTrue
from proveit.basiclogic.variables import A

# hypothesis: Not(Not(A))
hypothesis = Not(Not(A))
# [Not(Not(A)) = TRUE] assuming hypothesis
deriveStmtEqTrue(hypothesis).prove({hypothesis})
# [Not(A) = FALSE] assuming hypothesis
implicitNotF.specialize({A:Not(A)}).deriveConclusion().prove({hypothesis})
# A assuming hypothesis
implicitNotT.specialize().deriveConclusion().deriveViaBooleanEquality().prove({hypothesis})
# forall_{A} Not(Not(A)) => A
Implies(Not(Not(A)), A).generalize(A).qed(__file__)
