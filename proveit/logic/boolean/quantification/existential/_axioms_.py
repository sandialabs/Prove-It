from proveit.logic import TRUE, inBool, Forall, Exists, NotExists, Not, Equals, NotEquals
from proveit.common import P, Q, S, PxEtc, Qetc, xEtc, etc_QxEtc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

existsDef = Forall((P, Qetc, S), Equals(Exists(xEtc, PxEtc, S, etc_QxEtc), Not(Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc))))
existsDef

notExistsDef = Forall((P, Qetc, S), Equals(NotExists(xEtc, PxEtc, S, etc_QxEtc), Not(Exists(xEtc, PxEtc, S, etc_QxEtc))))
notExistsDef

endAxioms(locals(), __package__)