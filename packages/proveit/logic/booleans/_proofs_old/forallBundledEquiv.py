from proveit.basiclogic.booleans.theorems import forall_bundling, forall_unraveling
from proveit.basiclogic import Iff
from proveit.common import P, S, Qetc, Retc

# forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..}
# P(..x.., ..y..) => forall_{..x.., ..y.. in S | ..Q(..x..)..,
# ..R(..y..)..} P(..x.., ..y..)
forall_bundling_spec = forall_bundling.instantiate().proven()
# forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
# => forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..}
# P(..x.., ..y..)
forall_unraveling.instantiate().proven()
# lhs = forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
# rhs = forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
lhs, rhs = forall_bundling_spec.conclusion, forall_bundling_spec.hypothesis
# lhs in BOOLEANS, rhs in BOOLEANS
for expr in (lhs, rhs):
    expr.deduce_in_bool().proven()
# lhs = rhs
equiv = Iff(lhs, rhs).conclude_via_composition().derive_equality().proven()
# forall_{P, ..Q.., ..R.., S} [forall_{..x.., ..y.. in S | ..Q(..x..)..,
# ..R(..y..)..} P(..x.., ..y..) = forall_{..x.. in S | ..Q(..x..)..}
# forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)]
equiv.generalize((P, Qetc, Retc, S)).qed(__file__)
