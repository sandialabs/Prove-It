from proveit.basiclogic.booleans.theorems import doubleNegateConclusion
from proveit.basiclogic import Implies, Not, BOOLEANS, inBool
from proveit.common import A, B

# [Not(B) => Not(Not(A))] => [Not(A) => B)]  assuming inBool(B)
toConclusion = Implies(Not(B), Not(Not(A))).transposition()
# [Not(B) => A] => [Not(B) => Not(Not(A))] assuming inBool(A)
fromHyp = doubleNegateConclusion.instantiate({A:Not(B), B:A}).proven({inBool(A)})
# [Not(B) => A] => [Not(A)=>B] assuming inBool(A) and inBool(B)
transpositionExpr = fromHyp.applySyllogism(toConclusion).proven({inBool(A), inBool(B)})
# forall_{A, B in BOOLEANS} [Not(B) => A] => [Not(A)=>B]
transpositionExpr.generalize((A, B), domain=BOOLEANS).qed(__file__)
