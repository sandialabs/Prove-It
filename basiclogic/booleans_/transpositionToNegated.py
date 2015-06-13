from basiclogic import *

# [B => Not(Not(A))] => [Not(A)=>Not(B)] assuming inBool(A), inBool(B)
toConclusion = Implies(B, Not(Not(A))).transposition()
# [B => A] => [B => Not(Not(A))] assuming inBool(A)
fromHyp = booleans.doubleNegateConclusion.specialize({A:B, B:A}).prove({inBool(A)})
# [B => A] => [Not(A)=>Not(B)] assuming inBool(A), inBool(B)
transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
# forall_{A, B | inBool(A), inBool(B)} [B=>A] => [Not(A) => Not(B)]
booleans.qed('transpositionToNegated', transpositionExpr.generalize((A, B), (inBool(A), inBool(B))))
