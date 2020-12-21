from proveit.basiclogic.booleans.axioms import exists_def
from proveit.basiclogic import Exists, Forall, Not, NotEquals, Implies, In, TRUE, derive_stmt_eq_true
from proveit.common import P, S, X, x_etc, Px_etc, etc_Qx_etc, Qetc

in_domain = In(x_etc, S)  # ..x.. in S
# exists_not = [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))]
exists_not = Exists(x_etc, Not(Px_etc), S, etc_Qx_etc)
# [Not(forall_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) != TRUE] assuming exists_not
exists_def.instantiate({Px_etc: Not(Px_etc)}
                       ).derive_right_via_equality().proven({exists_not})
# forall_{..x.. in S | ..Q(..x..)..} P(..x..)
forall_px = Forall(x_etc, Px_etc, S, etc_Qx_etc)
# forall_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) != TRUE
forall_not_px_not_true = Forall(
    x_etc, NotEquals(
        Not(Px_etc), TRUE), S, etc_Qx_etc)
# forall_px in BOOLEANS, forall_not_px_not_true in BOOLEANS
for expr in (forall_px, forall_not_px_not_true):
    expr.deduce_in_bool().proven()
# Not(TRUE) != TRUE
NotEquals(Not(TRUE), TRUE).prove_by_eval()
# forall_not_px_not_true assuming forall_px, ..Q(..x..).., In(..x.., S)
derive_stmt_eq_true(
    forall_px.instantiate()).lhs_statement_substitution(
        NotEquals(
            Not(X),
            TRUE),
    X).derive_conclusion().generalize(
    x_etc,
    domain=S,
    conditions=etc_Qx_etc).proven(
    {
        forall_px,
        in_domain})
# Not(forall_not_px_not_true) => Not(forall_px)
Implies(forall_px, forall_not_px_not_true).transpose().proven()
# forall_{P, ..Q.., S} [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))]
# => [Not(forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
Implies(exists_not, Not(forall_px)).generalize((P, Qetc, S)).qed(__file__)
