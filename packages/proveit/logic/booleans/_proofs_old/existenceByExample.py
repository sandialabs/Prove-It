from proveit.basiclogic.booleans.axioms import existsDef
from proveit.basiclogic import Forall, NotEquals, Implies, TRUE, FALSE, deriveStmtEqTrue, In
from proveit.common import X, P, S, xEtc, yEtc, PxEtc, PyEtc, Qetc, etc_QxEtc, etc_QyEtc

inDomain = In(xEtc, S) # ..x.. in S

# neverPy = [forall_{..y.. in S | ..Q(..y..)..} (P(..y..) != TRUE)]
neverPy = Forall(yEtc, NotEquals(PyEtc, TRUE), S, etc_QyEtc)
# (P(..x..) != TRUE) assuming ..Q(..x..).., neverPy
neverPy.instantiate({yEtc:xEtc}).proven({etc_QxEtc, neverPy, inDomain})
# (TRUE != TRUE) assuming ..Q(..x..).., P(..x..), neverPy
trueNotEqTrue = deriveStmtEqTrue(PxEtc).subRightSideInto(NotEquals(X, TRUE), X).proven({etc_QxEtc, PxEtc, neverPy, inDomain})
# FALSE assuming ..Q(..x..).., P(..x..), neverPy
trueNotEqTrue.evaluation().deriveContradiction().deriveConclusion().proven({etc_QxEtc, PxEtc, neverPy, inDomain})
# [forall_{..y.. in S | ..Q(..y..)..} (P(..y..) != TRUE)] in BOOLEANS
neverPy.deduceInBool().proven()
# Not(forall_{..y.. in S | ..Q(..y..)..} (P(..y..) != TRUE) assuming ..Q(..x..).., P(..x..)
Implies(neverPy, FALSE).deriveViaContradiction().proven({etc_QxEtc, PxEtc, inDomain})
# exists_{..y.. in S | ..Q(..y..)..} P(..y..) assuming Q(..x..), P(..x..)
existence = existsDef.instantiate({xEtc:yEtc}).deriveLeftViaEquality().proven({etc_QxEtc, PxEtc, inDomain})
# forall_{P, ..Q.., S} forall_{..x.. in S | ..Q(..x..)..} [P(..x..) => exists_{..y.. in S | ..Q(..y..)..} P(..y..)]
Implies(PxEtc, existence).generalize(xEtc, S, etc_QxEtc).generalize((P, Qetc, S)).qed(__file__)
