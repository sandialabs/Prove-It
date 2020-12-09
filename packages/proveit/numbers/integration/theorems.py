from proveit.logic import Forall, Implies, InSet
from proveit.numbers import Real
from proveit.numbers import Integrate
from proveit.common import P, S, xEtc, PxEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

integrationClosure = Forall([P, S], Implies(Forall(xEtc, InSet(PxEtc, Real), domain=S), 
                                            InSet(Integrate(xEtc, PxEtc, domain=S), Real)))
integrationClosure

endTheorems(locals(), __package__)
