from basiclogic import *

# [TRUE or FALSE]
booleans.orTF.deriveViaBooleanEquality().prove()
# [TRUE or TRUE=FALSE] via [TRUE or FALSE] and TRUE != FALSE
booleans.trueNotFalse.unfold().equateNegatedToFalse().lhsSubstitute(X, Or(TRUE, X)).prove()
# [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
deriveStmtEqTrue(booleans.trueEqTrue).lhsSubstitute(X, Or(X, Equals(TRUE, FALSE))).prove()
# inBool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
booleans.qed('trueInBool', inBool(TRUE).concludeAsFolded())
