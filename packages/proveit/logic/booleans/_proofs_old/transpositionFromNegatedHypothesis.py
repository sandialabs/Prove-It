from proveit.basiclogic.booleans.theorems import double_negate_conclusion
from proveit.basiclogic import Implies, Not, BOOLEANS, in_bool
from proveit.common import A, B

# [Not(B) => Not(Not(A))] => [Not(A) => B)]  assuming in_bool(B)
to_conclusion = Implies(Not(B), Not(Not(A))).transposition()
# [Not(B) => A] => [Not(B) => Not(Not(A))] assuming in_bool(A)
from_hyp = double_negate_conclusion.instantiate({A:Not(B), B:A}).proven({in_bool(A)})
# [Not(B) => A] => [Not(A)=>B] assuming in_bool(A) and in_bool(B)
transposition_expr = from_hyp.apply_syllogism(to_conclusion).proven({in_bool(A), in_bool(B)})
# forall_{A, B in BOOLEANS} [Not(B) => A] => [Not(A)=>B]
transposition_expr.generalize((A, B), domain=BOOLEANS).qed(__file__)
