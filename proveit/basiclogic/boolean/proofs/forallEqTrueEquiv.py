from proveit.basiclogic import Forall, Iff, Equals, TRUE, deriveStmtEqTrue
from proveit.basiclogic.variables import P, S
from proveit.basiclogic.simpleExpr import xEtc, PxEtc, etcQ, etc_QxEtc

# forallPx = [forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
forallPx = Forall(xEtc, PxEtc, S, etc_QxEtc)
# forallPxEqT = [forall_{..x.. in S | ..Q(..x..)..} {P(..x..)=TRUE}]
forallPxEqT = Forall(xEtc, Equals(PxEtc, TRUE), S, etc_QxEtc)
# forallPxEqT assuming forallPx
deriveStmtEqTrue(forallPx.specialize()).generalize(xEtc, S, etc_QxEtc).prove({forallPx})
# forallPx assuming forallPxEqT
forallPxEqT.specialize().deriveViaBooleanEquality().generalize(xEtc, S, etc_QxEtc).prove({forallPxEqT})
# [forall_{..x.. in S | ..Q(..x..)..} P(..x..)] <=> [forall_{..x.. in S | ..Q(..x..)..} {P(..x..)=TRUE}]
iffForalls = Iff(forallPx, forallPxEqT).concludeViaComposition().prove()
# forallPx in BOOLEANS, forallPxEqT in BOOLEANS
for expr in (forallPx, forallPxEqT):
    expr.deduceInBool()
# forall_{P, ..Q.., S} [forall_{..x.. in S | ..Q(..x..)..} P(..x..)] = [forall_{..x.. in S | ..Q(..x..)..} {P(..x..)=TRUE}]
iffForalls.deriveEquality().generalize((P, etcQ, S)).qed(__file__)
