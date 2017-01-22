from proveit.logic import Forall, Or, Equals, InSet, Union
from proveit.common import A, B, Bmulti, Betc, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

unionDef = Forall((x, A, B), Equals(InSet(x, Union(A, B)), Or(InSet(x, A), InSet(x, B))))

unionComposition = Forall((A, Bmulti), Equals(Union(A, Betc), Union(A, Union(Betc))))

endAxioms(locals(), __package__)


