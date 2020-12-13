from proveit.basiclogic.booleans.theorems import forallBundling, forallUnraveling
from proveit.basiclogic import Iff
from proveit.common import P, S, Qetc, Retc

# forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..) => forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
forallBundlingSpec = forallBundling.instantiate().proven()
# forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) => forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
forallUnraveling.instantiate().proven()
# lhs = forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
# rhs = forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) 
lhs, rhs = forallBundlingSpec.conclusion, forallBundlingSpec.hypothesis
# lhs in BOOLEANS, rhs in BOOLEANS
for expr in (lhs, rhs): expr.deduceInBool().proven()
# lhs = rhs
equiv = Iff(lhs, rhs).concludeViaComposition().deriveEquality().proven()
# forall_{P, ..Q.., ..R.., S} [forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) = forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)]
equiv.generalize((P, Qetc, Retc, S)).qed(__file__)
