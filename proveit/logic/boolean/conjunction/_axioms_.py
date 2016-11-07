from proveit.logic import Equals, And, TRUE, FALSE, Forall, Implies
from proveit.common import A, B, Aetc, Betc, Cetc 
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

andTT = Equals(And(TRUE, TRUE), TRUE)
andTT

andTF = Equals(And(TRUE, FALSE), FALSE)
andTF

andFT = Equals(And(FALSE, TRUE), FALSE)
andFT

andFF = Equals(And(FALSE, FALSE), FALSE)
andFF

andComposition = Forall((A, Betc), Equals(And(A, Betc), And(A, And(Betc))))
andComposition

andImpliesEach = Forall((Aetc, B, Cetc), Implies(And(Aetc, B, Cetc), B))
andImpliesEach

endAxioms(locals(), __package__)
