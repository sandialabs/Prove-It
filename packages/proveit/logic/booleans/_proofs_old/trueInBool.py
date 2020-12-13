from proveit.basiclogic.booleans.axioms import orTF
from proveit.basiclogic.booleans.theorems import trueNotFalse, trueEqTrue
from proveit.basiclogic import TRUE, FALSE, inBool, Or, Equals, deriveStmtEqTrue
from proveit.common import X

# [TRUE or FALSE]
orTF.deriveViaBooleanEquality().proven()
# [TRUE or TRUE=FALSE] via [TRUE or FALSE] and TRUE != FALSE
trueNotFalse.unfold().equateNegatedToFalse().subLeftSideInto(Or(TRUE, X), X).proven()
# [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
deriveStmtEqTrue(trueEqTrue).subLeftSideInto(Or(X, Equals(TRUE, FALSE)), X).proven()
# inBool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
inBool(TRUE).concludeAsFolded().qed(__file__)
