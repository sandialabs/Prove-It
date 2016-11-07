from proveit.logic import Forall, Implies, Equals, TRUE, NotExists, NotEquals, Not, Exists, inBool
from proveit.common import P, S, Qetc, xEtc, yEtc, PxEtc, PyEtc, etc_QxEtc, etc_QyEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

existsDefNegation = Forall((P, Qetc, S), Equals(NotExists(xEtc, PxEtc, S, etc_QxEtc), Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc)))
existsDefNegation

notExistsUnfolding = Forall((P, Qetc, S), Implies(NotExists(xEtc, PxEtc, S, etc_QxEtc), Not(Exists(xEtc, PxEtc, S, etc_QxEtc))))
notExistsUnfolding

notExistsFolding = Forall((P, Qetc, S), Implies(Not(Exists(xEtc, PxEtc, S, etc_QxEtc)), NotExists(xEtc, PxEtc, S, etc_QxEtc)))
notExistsFolding

existsInBool = Forall((P, Qetc, S), inBool(Exists(xEtc, PxEtc, S, etc_QxEtc)))
existsInBool

existenceByExample = Forall((P, Qetc, S), Forall(xEtc, Implies(PxEtc, Exists(yEtc, PyEtc, S, etc_QyEtc)), S, etc_QxEtc))
existenceByExample

existsNotImpliesNotForall = Forall((P, Qetc, S), Implies(Exists(xEtc, Not(PxEtc), S, etc_QxEtc), Not(Forall(xEtc, PxEtc, S, etc_QxEtc))))
existsNotImpliesNotForall

endTheorems(locals(), __package__)
