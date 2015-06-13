from proveit.basiclogic import *

# A=TRUE assuming A
AeqT = deriveStmtEqTrue(A).prove({A})
# B=TRUE assuming B
BeqT = deriveStmtEqTrue(B).prove({B})
# TRUE AND TRUE
booleans.trueAndTrue
# (TRUE and B) assuming B via (TRUE and TRUE)
BeqT.lhsSubstitute(X, And(TRUE, X)).prove({B})
# (A and B) assuming A, B via (TRUE and TRUE)
AeqT.lhsSubstitute(X, And(X, B)).prove({A, B})
# forall_{A | A, B | B} (A and B)
booleans.qed('conjunctionIntro', And(A, B).generalize((A, B), (A, B)))
