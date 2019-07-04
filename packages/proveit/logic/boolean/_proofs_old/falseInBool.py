from proveit.basiclogic.boolean.axioms import orFT, falseNotTrue
from proveit.basiclogic.boolean.theorems import falseEqFalse
from proveit.basiclogic import FALSE, inBool, Or, Equals, deriveStmtEqTrue
from proveit.common import X

# [FALSE or TRUE]
orFT.deriveViaBooleanEquality().proven()
# [FALSE or FALSE=FALSE] via [FALSE or TRUE] and FALSE=FALSE
deriveStmtEqTrue(falseEqFalse).subLeftSideInto(Or(FALSE, X), X).proven()
# [FALSE=TRUE or FALSE=FALSE] via [FALSE or FALSE=FALSE] and Not(FALSE=TRUE)
falseNotTrue.unfold().equateNegatedToFalse().subLeftSideInto(Or(X, Equals(FALSE, FALSE)), X).proven()
# inBool(FALSE) via [FALSE=TRUE or FALSE=FALSE]
inBool(FALSE).concludeAsFolded().qed(__file__)
