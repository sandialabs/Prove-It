from proveit.logic import Forall, Implies, InSet
from proveit.number import Real
from proveit.number import Integrate
from proveit.common import P, S, xEtc, PxEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

integrationClosure = Forall([P, S], Implies(Forall(xEtc, InSet(PxEtc, Real), domain=S), 
                                            InSet(Integrate(xEtc, PxEtc, domain=S), Real)))
integrationClosure

endTheorems(locals(), __package__)
