from proveit.basiclogic.booleans.theorems import or_contradiction
from proveit.basiclogic import Implies, Not, Or, FALSE, in_bool
from proveit.common import A, B

# (A or B) => FALSE assuming Not(A), Not(B)
or_contradiction.instantiate().proven({Not(A), Not(B)})
# By contradiction: A assuming in_bool(A), A or B, Not(B)
Implies(Not(A), FALSE).derive_via_contradiction().proven({in_bool(A), Or(A, B), Not(B)})
# forall_{A, B | in_bool(A), Not(B)} (A or B) => A
Implies(Or(A, B), A).generalize((A, B), conditions=(in_bool(A), Not(B))).qed(__file__)
