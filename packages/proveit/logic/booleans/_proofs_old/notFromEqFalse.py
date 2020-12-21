from proveit.basiclogic.booleans.theorems import not_false
from proveit.basiclogic import Implies, Not, Equals, FALSE
from proveit.common import A, X

# AeqF := (A=F)
AeqF = Equals(A, FALSE)
# Not(FALSE)
not_false
# Not(A) assuming A=FALSE because Not(FALSE)
not_a = AeqF.sub_left_side_into(Not(X), X).proven({AeqF})
Implies(AeqF, not_a).generalize(A).qed(__file__)
