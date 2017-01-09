from proveit.logic import Forall, Implies, Equals, TRUE, NotExists, NotEquals, Not, Exists, inBool
from proveit.common import P, S, Qmulti, xMulti, Qetc, xEtc, yEtc, PxEtc, PyEtc, etc_QxEtc, etc_QyEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

existsDefNegation = Forall((P, Qmulti, S), Equals(NotExists(xMulti, PxEtc, S, etc_QxEtc), Forall(xMulti, NotEquals(PxEtc, TRUE), S, etc_QxEtc)))
existsDefNegation

notExistsUnfolding = Forall((P, Qmulti, S), Implies(NotExists(xMulti, PxEtc, S, etc_QxEtc), Not(Exists(xMulti, PxEtc, S, etc_QxEtc))))
notExistsUnfolding

notExistsFolding = Forall((P, Qmulti, S), Implies(Not(Exists(xMulti, PxEtc, S, etc_QxEtc)), NotExists(xMulti, PxEtc, S, etc_QxEtc)))
notExistsFolding

existsInBool = Forall((P, Qmulti, S), inBool(Exists(xMulti, PxEtc, S, etc_QxEtc)))
existsInBool

existenceByExample = Forall((P, Qmulti, S), Forall(xMulti, Implies(PxEtc, Exists(yEtc, PyEtc, S, etc_QyEtc)), S, etc_QxEtc))
existenceByExample

existsNotImpliesNotForall = Forall((P, Qmulti, S), Implies(Exists(xMulti, Not(PxEtc), S, etc_QxEtc), Not(Forall(xMulti, PxEtc, S, etc_QxEtc))))
existsNotImpliesNotForall

endTheorems(locals(), __package__)
