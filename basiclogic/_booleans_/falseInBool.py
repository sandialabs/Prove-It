from basiclogic import *

# [FALSE or TRUE]
booleans.orFT.deriveViaBooleanEquality().prove()
# [FALSE or FALSE=FALSE] via [FALSE or TRUE] and FALSE=FALSE
deriveStmtEqTrue(booleans.falseEqFalse).lhsSubstitute(X, Or(FALSE, X)).prove()
# [FALSE=TRUE or FALSE=FALSE] via [FALSE or FALSE=FALSE] and Not(FALSE=TRUE)
booleans.falseNotTrue.unfold().equateNegatedToFalse().lhsSubstitute(X, Or(X, Equals(FALSE, FALSE))).prove()
# inBool(FALSE) via [FALSE=TRUE or FALSE=FALSE]
booleans.qed('falseInBool', inBool(FALSE).concludeAsFolded())
