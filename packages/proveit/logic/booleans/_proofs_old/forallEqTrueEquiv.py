from proveit.basiclogic import Forall, Iff, Equals, TRUE, derive_stmt_eq_true
from proveit.common import P, S, x_etc, Px_etc, Qetc, etc_Qx_etc

# forall_px = [forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
forall_px = Forall(x_etc, Px_etc, S, etc_Qx_etc)
# forall_px_eq_t = [forall_{..x.. in S | ..Q(..x..)..} {P(..x..)=TRUE}]
forall_px_eq_t = Forall(x_etc, Equals(Px_etc, TRUE), S, etc_Qx_etc)
# forall_px_eq_t assuming forall_px
derive_stmt_eq_true(
    forall_px.instantiate()).generalize(
        x_etc,
        S,
        etc_Qx_etc).proven(
            {forall_px})
# forall_px assuming forall_px_eq_t
forall_px_eq_t.instantiate().derive_via_boolean_equality().generalize(
    x_etc, S, etc_Qx_etc).proven({forall_px_eq_t})
# [forall_{..x.. in S | ..Q(..x..)..} P(..x..)] <=> [forall_{..x.. in S | ..Q(..x..)..} {P(..x..)=TRUE}]
iff_foralls = Iff(
    forall_px,
    forall_px_eq_t).conclude_via_composition().proven()
# forall_px in BOOLEANS, forall_px_eq_t in BOOLEANS
for expr in (forall_px, forall_px_eq_t):
    expr.deduce_in_bool()
# forall_{P, ..Q.., S} [forall_{..x.. in S | ..Q(..x..)..} P(..x..)] =
# [forall_{..x.. in S | ..Q(..x..)..} {P(..x..)=TRUE}]
iff_foralls.derive_equality().generalize((P, Qetc, S)).qed(__file__)
