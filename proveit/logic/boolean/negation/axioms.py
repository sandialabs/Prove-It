from proveit.logic import Equals, Not, Implies, Forall, TRUE, FALSE, BOOLEANS
from proveit.common import A
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

notF = Equals(Not(FALSE), TRUE)
notF

notT = Equals(Not(TRUE), FALSE)
notT

implicitNotF = Forall(A, Implies(Equals(Not(A), TRUE), Equals(A, FALSE)))
implicitNotF

implicitNotT = Forall(A, Implies(Equals(Not(A), FALSE), Equals(A, TRUE)))
implicitNotT

contradictoryValidation = Forall(A, Implies(Implies(Not(A), FALSE), A), domain=BOOLEANS)
contradictoryValidation

endAxioms(locals(), __package__)
