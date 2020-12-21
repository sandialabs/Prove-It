from proveit.basiclogic import Implies, Not, in_bool
from proveit.common import A, B

# Not(Not(B)) assuming B and in_bool(B)
not_not_b = Not(Not(B)).conclude_via_double_negation()
# [A=>B] => [A => Not(Not(B))] assuming in_bool(B)
inner_expr = Implies(Implies(A, B), Implies(A, not_not_b)).proven({in_bool(B)})
# forall_{A, B | in_bool(B)}  [A=>B] => [A => Not(Not(B))]
inner_expr.generalize((A, B), conditions=in_bool(B)).qed(__file__)
