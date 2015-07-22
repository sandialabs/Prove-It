from proveit.basiclogic import Implies, Not, inBool
from proveit.common import A, B

# Not(Not(B)) assuming B and inBool(B)
notNotB = Not(Not(B)).concludeViaDoubleNegation()
# [A=>B] => [A => Not(Not(B))] assuming inBool(B)
innerExpr = Implies(Implies(A, B), Implies(A, notNotB)).prove({inBool(B)})
# forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
innerExpr.generalize((A, B), conditions=inBool(B)).qed(__file__)
