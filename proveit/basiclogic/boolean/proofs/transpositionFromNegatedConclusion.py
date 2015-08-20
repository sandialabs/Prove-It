from proveit.basiclogic import Implies, Not, FALSE, inBool, Equals, NotEquals
from proveit.common import A, B, X

# inBool(B=FALSE)
Equals(B, FALSE).deduceInBool()
# [Not(B=FALSE) => Not(A)] => [A => (B=FALSE)], using inBool(B=FALSE)
midPointBackHalf = Implies(Not(Equals(B, FALSE)), Not(A)).transposition()
# [(B != FALSE) => Not(A)] => [Not(B=FALSE) => Not(A)]
midPointFrontHalf = NotEquals(B, FALSE).definition().rhsStatementSubstitution(X, Implies(X, Not(A))).proven()
# [(B != FALSE) => Not(A)] => [A => (B=FALSE)]
midPoint = midPointFrontHalf.applySyllogism(midPointBackHalf).proven()
# B assuming (B != FALSE) and inBool(B)
notBeqF = NotEquals(B, FALSE)
notBeqF.deriveViaDoubleNegation().proven({notBeqF, inBool(B)})
# [B => Not(A)] => [(B != FALSE) => Not(A)] assuming inBool(B)
fromHyp = Implies(Implies(B, Not(A)), Implies(notBeqF, Not(A))).proven({inBool(B)})
# Not(B) assuming B=FALSE
BeqF = Equals(B, FALSE)
BeqF.deriveViaBooleanEquality().proven({BeqF})
# [A => (B=FALSE)] => [A => Not(B)] assuming inBool(B)
toConclusion = Implies(Implies(A, BeqF), Implies(A, Not(B))).proven({inBool(B)})
# [B => Not(A)] => [A=>Not(B)] assuming inBool(B)
transpositionExpr = fromHyp.applySyllogism(midPoint).applySyllogism(toConclusion).proven({inBool(B)})
# forall_{A, B | inBool(B)} [B => Not(A)] => [A=>Not(B)]
transpositionExpr.generalize((A, B), conditions=inBool(B)).qed(__file__)
