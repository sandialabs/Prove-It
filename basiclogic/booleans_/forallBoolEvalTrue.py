from basiclogic import *

# P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
folding = booleans.foldForallOverBool.specialize()
# forall_{P} [P(TRUE) and P(FALSE)] => {[forall_{A in BOOLEANS} P(A)] = TRUE}
booleans.qed('forallBoolEvalTrue', Implies(folding.hypothesis, deriveStmtEqTrue(folding.deriveConclusion())).generalize(P))
