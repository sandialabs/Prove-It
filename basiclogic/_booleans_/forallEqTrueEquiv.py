from basiclogic import *

# forallPx = [forall_{x* | Q*(x*)} P(x*)]
forallPx = Forall(xStar, P_of_xStar, multiQ_of_xStar)
# forallPxEqT = [forall_{x* | Q*(x*)} {P(x*)=TRUE}]
forallPxEqT = Forall(xStar, Equals(P_of_xStar, TRUE), multiQ_of_xStar)
# forallPxEqT assuming forallPx
deriveStmtEqTrue(forallPx.specialize()).generalize(xStar, multiQ_of_xStar).prove({forallPx})
# forallPx assuming forallPxEqT
forallPxEqT.specialize().deriveViaBooleanEquality().generalize(xStar, multiQ_of_xStar).prove({forallPxEqT})
# [forall_{x* | Q*(x*)} P(x*)] <=> [forall_{x* | Q*(x*)} {P(x*)=TRUE}]
iffForalls = Iff(forallPx, forallPxEqT).concludeViaComposition().prove()
# forallPx in BOOLEANS, forallPxEqT in BOOLEANS
for expr in (forallPx, forallPxEqT):
    expr.deduceInBool()
# forall_{P, Q*} [forall_{x* | Q*(x*)} P(x*)] = [forall_{x* | Q*(x*)} {P(x*)=TRUE}]
booleans.qed('forallEqTrueEquiv', iffForalls.deriveEquality().generalize((P, multiQ)))
