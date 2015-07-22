from proveit.basiclogic.boolean.axioms import existsDef, notExistsDef
from proveit.basiclogic import Forall, Not, NotEquals, TRUE
from proveit.basiclogic.variables import X, P, S
from proveit.basiclogic.simpleExpr import xEtc, etcQ, PxEtc, etc_QxEtc

# [exists_{..x.. in S | ..Q(..x..)..} P(..x..)] = not(forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
existsDefSpec = existsDef.specialize().prove()
# notexists_{..x.. in S | ..Q..(..x..)} P(..x..) = not[exists_{..x.. in S | ..Q(..x..)..} P(..x..)]
notExistsDefSpec = notExistsDef.specialize().prove()
# rhs = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)
rhs = Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc)
# [forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)] in BOOLEANS
rhs.deduceInBool().prove()
# not(not(forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))) = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
doubleNegatedForall = Not(Not(rhs)).deduceDoubleNegationEquiv().deriveReversed().prove()
# notexists_{..x.. in S | ..Q(..x..)..} P(..x..) = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE))
equiv = notExistsDefSpec.applyTransitivity(existsDefSpec.substitution(X, Not(X))).applyTransitivity(doubleNegatedForall).prove()
# forall_{P, ..Q..} [notexists_{..x.. in S | ..Q(..x..)..} P(..x..) = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)]
equiv.generalize((P, etcQ, S)).qed(__file__)
