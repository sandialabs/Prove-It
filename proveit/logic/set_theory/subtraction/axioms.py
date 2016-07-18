from proveit.logic import Forall, Or, Iff, And, InSet, NotInSet, Difference
from proveit.common import A, B, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

differenceDef = Forall((x, A, B), Iff(InSet(x, Difference(A, B)), 
                                      And(InSet(x, A), NotInSet(x, B))))
differenceDef

endAxioms(locals(), __package__)


