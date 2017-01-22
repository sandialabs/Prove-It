from proveit.logic import Forall, Not, Equals, InSet, NotInSet, NOTHING
from proveit.common import x, S, f
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

allNotInNothing = Forall(x, NotInSet(x, NOTHING))
allNotInNothing

notInSetDef = Forall((x, S), Equals(NotInSet(x, S), Not(InSet(x, S))))
notInSetDef

endAxioms(locals(), __package__)
