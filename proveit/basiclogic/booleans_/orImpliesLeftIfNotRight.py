from proveit.basiclogic import *

# (A or B) => FALSE assuming Not(A), Not(B)
booleans.orContradiction.specialize().prove({Not(A), Not(B)})
# By contradiction: A assuming inBool(A), A or B, Not(B)
Implies(Not(A), FALSE).deriveViaContradiction().prove({inBool(A), Or(A, B), Not(B)})
# forall_{A, B | inBool(A), Not(B)} (A or B) => A
booleans.qed('orImpliesLeftIfNotRight', Implies(Or(A, B), A).generalize((A, B), (inBool(A), Not(B))))
