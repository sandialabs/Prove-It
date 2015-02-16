from basiclogic import *

# hypothesis = [Not(B) => Not(A)]
hypothesis = Implies(Not(B), Not(A))
# A=FALSE assuming Not(B)=>Not(A) and Not(B)
AeqF = Not(A).equateNegatedToFalse().prove({hypothesis, Not(B)})
# FALSE assuming Not(B)=>Not(A), Not(B), and A
AeqF.deriveRightViaEquivalence().prove({hypothesis, Not(B), A})
# B assuming inBool(B), (Not(B)=>Not(A)), A
Implies(Not(B), FALSE).deriveViaContradiction().prove({inBool(B), hypothesis, A})
# [Not(B) => Not(A)] => [A => B] by nested hypothetical reasoning assuming inBool(B)
transpositionExpr = Implies(hypothesis, Implies(A, B)).prove({inBool(B)})
# forall_{A, B | inBool(B)} [A => B] => [Not(B) => Not(A)]
booleans.qed('transpositionFromNegated', transpositionExpr.generalize((A, B), inBool(B)))
