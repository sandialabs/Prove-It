from proveit.basiclogic.booleans.axioms import exists_def, not_exists_def
from proveit.basiclogic import Forall, Not, NotEquals, TRUE
from proveit.common import X, P, S, x_etc, Qetc, Px_etc, etc_Qx_etc

# [exists_{..x.. in S | ..Q(..x..)..} P(..x..)] = not(forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
exists_def_spec = exists_def.instantiate().proven()
# notexists_{..x.. in S | ..Q..(..x..)} P(..x..) = not[exists_{..x.. in S
# | ..Q(..x..)..} P(..x..)]
not_exists_def_spec = not_exists_def.instantiate().proven()
# rhs = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)
rhs = Forall(x_etc, NotEquals(Px_etc, TRUE), S, etc_Qx_etc)
# [forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)] in BOOLEANS
rhs.deduce_in_bool().proven()
# not(not(forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))) =
# forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
double_negated_forall = Not(
    Not(rhs)).deduce_double_negation_equiv().derive_reversed().proven()
# notexists_{..x.. in S | ..Q(..x..)..} P(..x..) = forall_{..x.. in S |
# ..Q(..x..)..} (P(..x..) != TRUE))
equiv = not_exists_def_spec.apply_transitivity(exists_def_spec.substitution(
    Not(X), X)).apply_transitivity(double_negated_forall).proven()
# forall_{P, ..Q..} [notexists_{..x.. in S | ..Q(..x..)..} P(..x..) =
# forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)]
equiv.generalize((P, Qetc, S)).qed(__file__)
