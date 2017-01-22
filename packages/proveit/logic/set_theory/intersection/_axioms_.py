from proveit.logic import Forall, Equals, And, InSet, Intersect
from proveit.common import A, B, Bmulti, Betc, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

intersectionDef = Forall((x, A, B), Equals(InSet(x, Intersect(A, B)), And(InSet(x, A), InSet(x, B))))
intersectionDef

intersectionComposition = Forall((A, Bmulti), Equals(Intersect(A, Betc), Intersect(A, Intersect(Betc))))
intersectionComposition

endAxioms(locals(), __package__)


