from proveit.logic import Forall, Implies, InSet
from proveit.number import Reals
from proveit.number import Integrate
from proveit.common import P, S, xEtc, PxEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

integrationClosure = Forall([P, S], Implies(Forall(xEtc, InSet(PxEtc, Reals), domain=S), 
                                            InSet(Integrate(xEtc, PxEtc, domain=S), Reals)))
integrationClosure

endTheorems(locals(), __package__)
