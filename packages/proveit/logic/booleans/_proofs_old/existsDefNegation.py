from proveit.basiclogic.booleans.axioms import existsDef, notExistsDef
from proveit.basiclogic import Forall, Not, NotEquals, TRUE
from proveit.common import X, P, S, xEtc, Qetc, PxEtc, etc_QxEtc

# [exists_{..x.. in S | ..Q(..x..)..} P(..x..)] = not(forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
existsDefSpec = existsDef.instantiate().proven()
# notexists_{..x.. in S | ..Q..(..x..)} P(..x..) = not[exists_{..x.. in S | ..Q(..x..)..} P(..x..)]
notExistsDefSpec = notExistsDef.instantiate().proven()
# rhs = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)
rhs = Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc)
# [forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)] in BOOLEANS
rhs.deduceInBool().proven()
# not(not(forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))) = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
doubleNegatedForall = Not(Not(rhs)).deduceDoubleNegationEquiv().deriveReversed().proven()
# notexists_{..x.. in S | ..Q(..x..)..} P(..x..) = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
equiv = notExistsDefSpec.applyTransitivity(existsDefSpec.substitution(Not(X), X)).applyTransitivity(doubleNegatedForall).proven()
# forall_{P, ..Q..} [notexists_{..x.. in S | ..Q(..x..)..} P(..x..) = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)]
equiv.generalize((P, Qetc, S)).qed(__file__)
