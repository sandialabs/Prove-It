from proveit.logic import Equals, Implies, TRUE, FALSE, Forall, And, Iff
from proveit.common import A, B
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

impliesTF = Equals(Implies(TRUE, FALSE), FALSE)
impliesTF

iffDef = Forall((A, B), Equals(Iff(A, B), And(Implies(A, B), Implies(B, A))))
iffDef

endAxioms(locals(), __package__)
