from proveit.basiclogic.booleans.axioms import or_f_f
from proveit.basiclogic.booleans.theorems import not_false
from proveit.basiclogic import Implies, Not, Or, FALSE
from proveit.common import A, B, X

# Not(A or B) = Not(F or B) assuming Not(A)
not_aor_b_eq_not_forB = Not(A).equate_negated_to_false().substitution(Not(Or(X, B)), X).proven({Not(A)})
# Not(A or B) = Not(F or F) assuming Not(A), Not(B)
not_aor_b_eq_not_forF = not_aor_b_eq_not_forB.apply_transitivity(Not(B).equate_negated_to_false().substitution(Not(Or(FALSE, X)), X)).proven({Not(A), Not(B)})
#  Not(A or B) = Not(F) assuming Not(A), Not(B)
not_aor_b_eq_not_f = not_aor_b_eq_not_forF.apply_transitivity(or_f_f.substitution(Not(X), X)).proven({Not(A), Not(B)})
# Not(FALSE)
not_false
# Not(A or B) assuming Not(A), Not(B)
not_aor_b = not_aor_b_eq_not_f.derive_left_via_equality().proven({Not(A), Not(B)})
# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
Implies(Not(A), Implies(Not(B), not_aor_b)).generalize((A, B)).qed(__file__)
