from proveit.basiclogic.boolean.theorems import notFalse
from proveit.basiclogic import Implies, Not, Equals, FALSE
from proveit.basiclogic.variables import A, X

# AeqF := (A=F)
AeqF = Equals(A, FALSE)
# Not(FALSE)
notFalse
# Not(A) assuming A=FALSE because Not(FALSE)
notA = AeqF.lhsSubstitute(X, Not(X)).prove({AeqF})
Implies(AeqF, notA).generalize(A).qed(__file__)
