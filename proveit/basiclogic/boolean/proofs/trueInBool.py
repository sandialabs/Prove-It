from proveit.basiclogic.boolean.axioms import orTF
from proveit.basiclogic.boolean.theorems import trueNotFalse, trueEqTrue
from proveit.basiclogic import TRUE, FALSE, inBool, Or, Equals, deriveStmtEqTrue
from proveit.common import X

# [TRUE or FALSE]
orTF.deriveViaBooleanEquality().proven()
# [TRUE or TRUE=FALSE] via [TRUE or FALSE] and TRUE != FALSE
trueNotFalse.unfold().equateNegatedToFalse().lhsSubstitute(X, Or(TRUE, X)).proven()
# [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
deriveStmtEqTrue(trueEqTrue).lhsSubstitute(X, Or(X, Equals(TRUE, FALSE))).proven()
# inBool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
inBool(TRUE).concludeAsFolded().qed(__file__)
