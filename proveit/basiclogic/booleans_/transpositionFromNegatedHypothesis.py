from proveit.basiclogic import *

# [Not(B) => Not(Not(A))] => [Not(A) => B)]  assuming inBool(B)
toConclusion = Implies(Not(B), Not(Not(A))).transposition()
# [Not(B) => A] => [Not(B) => Not(Not(A))] assuming inBool(A)
fromHyp = booleans.doubleNegateConclusion.specialize({A:Not(B), B:A}).prove({inBool(A)})
# [Not(B) => A] => [Not(A)=>B] assuming inBool(A) and inBool(B)
transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
# forall_{A, B | inBool(A), inBool(B)} [Not(B) => A] => [Not(A)=>B]
booleans.qed('transpositionFromNegatedHypothesis', transpositionExpr.generalize((A, B), (inBool(A), inBool(B))))
