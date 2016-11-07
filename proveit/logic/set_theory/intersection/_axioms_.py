from proveit.logic import Forall, Or, Iff, Equals, And, InSet, Intersect
from proveit.common import A, B, Cetc, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

intersectionDef = Forall((x, A, B), Iff(InSet(x, Intersect(A, B)), And(InSet(x, A), InSet(x, B))))
intersectionDef

intersectionComposition = Forall((A, B, Cetc), Equals(Intersect(A, B, Cetc), Intersect(A, Intersect(B, Cetc))))
intersectionComposition

endAxioms(locals(), __package__)


