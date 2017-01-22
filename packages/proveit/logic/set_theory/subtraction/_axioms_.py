from proveit.logic import Forall, Equals, And, InSet, NotInSet, Difference
from proveit.common import A, B, x
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

differenceDef = Forall((x, A, B), Equals(InSet(x, Difference(A, B)), 
                                      And(InSet(x, A), NotInSet(x, B))))

endAxioms(locals(), __package__)


