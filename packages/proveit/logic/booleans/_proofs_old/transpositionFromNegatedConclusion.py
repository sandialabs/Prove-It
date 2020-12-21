from proveit.basiclogic import Implies, Not, FALSE, in_bool, Equals, NotEquals
from proveit.common import A, B, X

# in_bool(B=FALSE)
Equals(B, FALSE).deduce_in_bool()
# [Not(B=FALSE) => Not(A)] => [A => (B=FALSE)], using in_bool(B=FALSE)
mid_point_back_half = Implies(Not(Equals(B, FALSE)), Not(A)).transposition()
# [(B != FALSE) => Not(A)] => [Not(B=FALSE) => Not(A)]
mid_point_front_half = NotEquals(B, FALSE).definition().rhs_statement_substitution(Implies(X, Not(A)), X).proven()
# [(B != FALSE) => Not(A)] => [A => (B=FALSE)]
mid_point = mid_point_front_half.apply_syllogism(mid_point_back_half).proven()
# B assuming (B != FALSE) and in_bool(B)
not_beq_f = NotEquals(B, FALSE)
not_beq_f.derive_via_double_negation().proven({not_beq_f, in_bool(B)})
# [B => Not(A)] => [(B != FALSE) => Not(A)] assuming in_bool(B)
from_hyp = Implies(Implies(B, Not(A)), Implies(not_beq_f, Not(A))).proven({in_bool(B)})
# Not(B) assuming B=FALSE
BeqF = Equals(B, FALSE)
BeqF.derive_via_boolean_equality().proven({BeqF})
# [A => (B=FALSE)] => [A => Not(B)] assuming in_bool(B)
to_conclusion = Implies(Implies(A, BeqF), Implies(A, Not(B))).proven({in_bool(B)})
# [B => Not(A)] => [A=>Not(B)] assuming in_bool(B)
transposition_expr = from_hyp.apply_syllogism(mid_point).apply_syllogism(to_conclusion).proven({in_bool(B)})
# forall_{A, B | in_bool(B)} [B => Not(A)] => [A=>Not(B)]
transposition_expr.generalize((A, B), conditions=in_bool(B)).qed(__file__)
