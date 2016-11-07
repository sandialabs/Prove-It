from proveit.logic import Forall, inBool
from proveit.common import P, S, xEtc, Qetc, PxEtc, etc_QxEtc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

forallInBool = Forall((P, Qetc, S), inBool(Forall(xEtc, PxEtc, S, etc_QxEtc)))
forallInBool

endAxioms(locals(), __package__)