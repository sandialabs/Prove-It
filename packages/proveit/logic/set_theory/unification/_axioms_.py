from proveit.logic import Forall, Or, Equals, InSet, Union
from proveit.common import A, B, Cetc, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

unionDef = Forall((x, A, B), Equals(InSet(x, Union(A, B)), Or(InSet(x, A), InSet(x, B))))
unionDef

unionComposition = Forall((A, B, Cetc), Equals(Union(A, B, Cetc), Union(A, Union(B, Cetc))))
unionComposition

endAxioms(locals(), __package__)


