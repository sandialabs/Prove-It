from proveit.basiclogic import *

# (A or B) => FALSE assuming Not(A), Not(B)
booleans.orContradiction.specialize().prove({Not(A), Not(B)})
# By contradiction: B assuming inBool(B), (A or B), Not(A)
Implies(Not(B), FALSE).deriveViaContradiction().prove({inBool(B), Or(A, B), Not(A)})
# forall_{A, B | Not(A), inBool(B)} (A or B) => B
booleans.qed('orImpliesRightIfNotLeft', Implies(Or(A, B), B).generalize((A, B), (Not(A), inBool(B))))
