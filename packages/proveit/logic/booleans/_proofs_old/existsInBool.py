from proveit.basiclogic.booleans.axioms import exists_def
from proveit.basiclogic import Equals, Or
from proveit.common import P, S, X, Qetc

# exists_{..x.. in S | ..Q(..x..)..} P(..x..) = not(forall_{..x.. |
# ..Q(..x..)..} P(..x..) != TRUE)
exists_def_spec = exists_def.instantiate().proven()
# [not(forall_{..x.. in S | ..Q(..x..)..} P(..x..) != TRUE) = TRUE] or [not(forall_{..x.. in S| ..Q(..x..)..} P(..x..) != TRUE) = FALSE]
rhs_true, rhs_false = exists_def_spec.rhs.deduce_in_bool().unfold().proven().operands
# exists_{..x.. in S | ..Q(..x..)..} P(..x..) in BOOLEANS assuming
# [not(forall_{..x.. in S | ..Q(..x..)..} P(..x..) != TRUE) = TRUE]
exists_in_bool_spec = rhs_true.sub_right_side_into(
    Equals(
        exists_def_spec.lhs,
        X),
    X).in_bool_via_boolean_equality().proven(
    {rhs_true})
# exists_{..x.. | ..Q(..x..)..} P(..x..) in BOOLEANS assuming
# [not(forall_{..x.. in S | ..Q..(..x..)} P(..x..) != TRUE) = FALSE]
rhs_false.sub_right_side_into(
    Equals(
        exists_def_spec.lhs,
        X),
    X).in_bool_via_boolean_equality().proven(
    {rhs_false})
# deduce rhs_true, rhs_fals, exists_in_bool_spec all in BOOLEANS
for expr in (rhs_true, rhs_false, exists_in_bool_spec):
    expr.deduce_in_bool()
# forall_{P, ..Q.., S} exists_{..x.. | ..Q(..x..)..} P(..x..) in BOOLEANS
Or(rhs_true, rhs_false).derive_common_conclusion(
    exists_in_bool_spec).generalize((P, Qetc, S)).qed(__file__)
