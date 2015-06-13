from proveit.basiclogic import *

# Not(Not(B)) assuming B and inBool(B)
notNotB = Not(Not(B)).concludeViaDoubleNegation()
# [A=>B] => [A => Not(Not(B))] assuming inBool(B)
innerExpr = Implies(Implies(A, B), Implies(A, notNotB)).prove({inBool(B)})
# forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
booleans.qed('doubleNegateConclusion', innerExpr.generalize((A, B), inBool(B)))
