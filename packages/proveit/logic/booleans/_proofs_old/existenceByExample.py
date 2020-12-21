from proveit.basiclogic.booleans.axioms import exists_def
from proveit.basiclogic import Forall, NotEquals, Implies, TRUE, FALSE, derive_stmt_eq_true, In
from proveit.common import X, P, S, x_etc, y_etc, Px_etc, Py_etc, Qetc, etc_Qx_etc, etc_Qy_etc

in_domain = In(x_etc, S)  # ..x.. in S

# never_py = [forall_{..y.. in S | ..Q(..y..)..} (P(..y..) != TRUE)]
never_py = Forall(y_etc, NotEquals(Py_etc, TRUE), S, etc_Qy_etc)
# (P(..x..) != TRUE) assuming ..Q(..x..).., never_py
never_py.instantiate({y_etc: x_etc}).proven({etc_Qx_etc, never_py, in_domain})
# (TRUE != TRUE) assuming ..Q(..x..).., P(..x..), never_py
true_not_eq_true = derive_stmt_eq_true(Px_etc).sub_right_side_into(
    NotEquals(X, TRUE), X).proven({etc_Qx_etc, Px_etc, never_py, in_domain})
# FALSE assuming ..Q(..x..).., P(..x..), never_py
true_not_eq_true.evaluation().derive_contradiction().derive_conclusion().proven(
    {etc_Qx_etc, Px_etc, never_py, in_domain})
# [forall_{..y.. in S | ..Q(..y..)..} (P(..y..) != TRUE)] in BOOLEANS
never_py.deduce_in_bool().proven()
# Not(forall_{..y.. in S | ..Q(..y..)..} (P(..y..) != TRUE) assuming
# ..Q(..x..).., P(..x..)
Implies(never_py, FALSE).derive_via_contradiction().proven(
    {etc_Qx_etc, Px_etc, in_domain})
# exists_{..y.. in S | ..Q(..y..)..} P(..y..) assuming Q(..x..), P(..x..)
existence = exists_def.instantiate({x_etc: y_etc}).derive_left_via_equality(
).proven({etc_Qx_etc, Px_etc, in_domain})
# forall_{P, ..Q.., S} forall_{..x.. in S | ..Q(..x..)..} [P(..x..) =>
# exists_{..y.. in S | ..Q(..y..)..} P(..y..)]
Implies(
    Px_etc, existence).generalize(
        x_etc, S, etc_Qx_etc).generalize(
            (P, Qetc, S)).qed(__file__)
