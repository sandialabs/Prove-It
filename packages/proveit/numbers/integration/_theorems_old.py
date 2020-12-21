from proveit.logic import Forall, Implies, InSet
from proveit.numbers import Real
from proveit.numbers import Integrate
from proveit.common import P, S, x_etc, Px_etc
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

integration_closure = Forall([P, S], Implies(Forall(x_etc, InSet(Px_etc, Real), domain=S), 
                                            InSet(Integrate(x_etc, Px_etc, domain=S), Real)))
integration_closure

end_theorems(locals(), __package__)
