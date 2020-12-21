from proveit.basiclogic.booleans.theorems import or_contradiction
from proveit.basiclogic import Implies, Not, Or, FALSE, in_bool
from proveit.common import A, B

# (A or B) => FALSE assuming Not(A), Not(B)
or_contradiction.instantiate().proven({Not(A), Not(B)})
# By contradiction: B assuming in_bool(B), (A or B), Not(A)
Implies(Not(B), FALSE).derive_via_contradiction().proven(
    {in_bool(B), Or(A, B), Not(A)})
# forall_{A, B | Not(A), in_bool(B)} (A or B) => B
Implies(Or(A, B), B).generalize(
    (A, B), conditions=(Not(A), in_bool(B))).qed(__file__)
