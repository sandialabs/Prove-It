from proveit.basiclogic.boolean.theorems import foldForallOverBool
from proveit.basiclogic import Implies, deriveStmtEqTrue
from proveit.common import P

# P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
folding = foldForallOverBool.specialize()
# forall_{P} [P(TRUE) and P(FALSE)] => {[forall_{A in BOOLEANS} P(A)] = TRUE}
Implies(folding.hypothesis, deriveStmtEqTrue(folding.deriveConclusion())).generalize(P).qed(__file__)
