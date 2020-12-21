from proveit.basiclogic.booleans.theorems import double_negate_conclusion
from proveit.basiclogic import Implies, Not, BOOLEANS, in_bool
from proveit.common import A, B

# [B => Not(Not(A))] => [Not(A)=>Not(B)] assuming in_bool(A), in_bool(B)
to_conclusion = Implies(B, Not(Not(A))).transposition()
# [B => A] => [B => Not(Not(A))] assuming in_bool(A)
from_hyp = double_negate_conclusion.instantiate(
    {A: B, B: A}).proven({in_bool(A)})
# [B => A] => [Not(A)=>Not(B)] assuming in_bool(A), in_bool(B)
transposition_expr = from_hyp.apply_syllogism(
    to_conclusion).proven({in_bool(A), in_bool(B)})
# forall_{A, B in BOOLEANS} [B=>A] => [Not(A) => Not(B)]
transposition_expr.generalize((A, B), domain=BOOLEANS).qed(__file__)
