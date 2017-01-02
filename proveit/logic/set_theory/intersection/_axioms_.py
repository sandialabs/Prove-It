from proveit.logic import Forall, Equals, And, InSet, Intersect
from proveit.common import A, B, Cmulti, Cetc, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

intersectionDef = Forall((x, A, B), Equals(InSet(x, Intersect(A, B)), And(InSet(x, A), InSet(x, B))))
intersectionDef

intersectionComposition = Forall((A, B, Cmulti), Equals(Intersect(A, B, Cetc), Intersect(A, Intersect(B, Cetc))))
intersectionComposition

endAxioms(locals(), __package__)


