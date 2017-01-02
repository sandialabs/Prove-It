from proveit.logic import Forall, inBool, Equals
from proveit._generic_ import Len
from proveit.number import Naturals
from proveit.common import n, P, S, Qmulti, xMulti, xEtc, PxEtc, etc_QxEtc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

forallInBool = Forall((P, Qmulti, S), inBool(Forall(xMulti, PxEtc, S, etc_QxEtc)))
forallInBool

# Forall_{P} [Forall_{x*} P(x*) = Forall_{n in naturals} Forall_{x* | |x*|=n} P(x*)
forallAnyNumberVars = Forall(P, Equals(Forall(xMulti, PxEtc), Forall(n, Forall(xMulti, PxEtc, conditions=Equals(Len(xEtc), n)), domain=Naturals)))
forallAnyNumberVars

endAxioms(locals(), __package__)