from proveit.basiclogic.booleans.theorems import doubleNegateConclusion
from proveit.basiclogic import Implies, Not, BOOLEANS, inBool
from proveit.common import A, B

# [B => Not(Not(A))] => [Not(A)=>Not(B)] assuming inBool(A), inBool(B)
toConclusion = Implies(B, Not(Not(A))).transposition()
# [B => A] => [B => Not(Not(A))] assuming inBool(A)
fromHyp = doubleNegateConclusion.instantiate({A:B, B:A}).proven({inBool(A)})
# [B => A] => [Not(A)=>Not(B)] assuming inBool(A), inBool(B)
transpositionExpr = fromHyp.applySyllogism(toConclusion).proven({inBool(A), inBool(B)})
# forall_{A, B in BOOLEANS} [B=>A] => [Not(A) => Not(B)]
transpositionExpr.generalize((A, B), domain=BOOLEANS).qed(__file__)
