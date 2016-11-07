from proveit.logic import Forall, Or, Iff, Equals, InSet, SubsetEq, SupersetEq
from proveit.common import A, B, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

subsetDef = Forall((A, B), Iff(SubsetEq(A, B), Forall(x, InSet(x, B), A)))
subsetDef

supersetDef = Forall((A, B), Iff(SupersetEq(A, B), Forall(x, InSet(x, A), B)))
supersetDef

endAxioms(locals(), __package__)


