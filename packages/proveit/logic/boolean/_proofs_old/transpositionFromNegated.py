from proveit.basiclogic import Implies, Not, FALSE, inBool
from proveit.common import A, B

# hypothesis = [Not(B) => Not(A)]
hypothesis = Implies(Not(B), Not(A))
# A=FALSE assuming Not(B)=>Not(A) and Not(B)
AeqF = Not(A).equateNegatedToFalse().proven({hypothesis, Not(B)})
# FALSE assuming Not(B)=>Not(A), Not(B), and A
AeqF.deriveRightViaEquivalence().proven({hypothesis, Not(B), A})
# B assuming inBool(B), (Not(B)=>Not(A)), A
Implies(Not(B), FALSE).deriveViaContradiction().proven({inBool(B), hypothesis, A})
# [Not(B) => Not(A)] => [A => B] by nested hypothetical reasoning assuming inBool(B)
transpositionExpr = Implies(hypothesis, Implies(A, B)).proven({inBool(B)})
# forall_{A, B | inBool(B)} [A => B] => [Not(B) => Not(A)]
transpositionExpr.generalize((A, B), conditions=inBool(B)).qed(__file__)
