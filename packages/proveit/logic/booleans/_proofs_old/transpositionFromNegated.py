from proveit.basiclogic import Implies, Not, FALSE, in_bool
from proveit.common import A, B

# hypothesis = [Not(B) => Not(A)]
hypothesis = Implies(Not(B), Not(A))
# A=FALSE assuming Not(B)=>Not(A) and Not(B)
AeqF = Not(A).equate_negated_to_false().proven({hypothesis, Not(B)})
# FALSE assuming Not(B)=>Not(A), Not(B), and A
AeqF.derive_right_via_equality().proven({hypothesis, Not(B), A})
# B assuming in_bool(B), (Not(B)=>Not(A)), A
Implies(Not(B), FALSE).derive_via_contradiction().proven(
    {in_bool(B), hypothesis, A})
# [Not(B) => Not(A)] => [A => B] by nested hypothetical reasoning assuming in_bool(B)
transposition_expr = Implies(hypothesis, Implies(A, B)).proven({in_bool(B)})
# forall_{A, B | in_bool(B)} [A => B] => [Not(B) => Not(A)]
transposition_expr.generalize((A, B), conditions=in_bool(B)).qed(__file__)
