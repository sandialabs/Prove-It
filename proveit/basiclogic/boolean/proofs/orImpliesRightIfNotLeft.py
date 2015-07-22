from proveit.basiclogic.boolean.theorems import orContradiction
from proveit.basiclogic import Implies, Not, Or, FALSE, inBool
from proveit.common import A, B

# (A or B) => FALSE assuming Not(A), Not(B)
orContradiction.specialize().prove({Not(A), Not(B)})
# By contradiction: B assuming inBool(B), (A or B), Not(A)
Implies(Not(B), FALSE).deriveViaContradiction().prove({inBool(B), Or(A, B), Not(A)})
# forall_{A, B | Not(A), inBool(B)} (A or B) => B
Implies(Or(A, B), B).generalize((A, B), conditions=(Not(A), inBool(B))).qed(__file__)
