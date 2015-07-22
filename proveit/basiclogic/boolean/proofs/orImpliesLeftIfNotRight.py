from proveit.basiclogic.boolean.theorems import orContradiction
from proveit.basiclogic import Implies, Not, Or, FALSE, inBool
from proveit.basiclogic.variables import A, B

# (A or B) => FALSE assuming Not(A), Not(B)
orContradiction.specialize().prove({Not(A), Not(B)})
# By contradiction: A assuming inBool(A), A or B, Not(B)
Implies(Not(A), FALSE).deriveViaContradiction().prove({inBool(A), Or(A, B), Not(B)})
# forall_{A, B | inBool(A), Not(B)} (A or B) => A
Implies(Or(A, B), A).generalize((A, B), conditions=(inBool(A), Not(B))).qed(__file__)
