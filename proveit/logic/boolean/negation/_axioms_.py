from proveit.logic import Equals, Not, Implies, Forall, TRUE, FALSE, Booleans, inBool
from proveit.common import A
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

notF = Equals(Not(FALSE), TRUE)
notF

notT = Equals(Not(TRUE), FALSE)
notT

negationForBooleansOnly = Forall(A, inBool(A), conditions=inBool(Not(A)))

affirmViaContradiction = Forall(A, Implies(Implies(Not(A), FALSE), A), domain=Booleans)
affirmViaContradiction

endAxioms(locals(), __package__)
