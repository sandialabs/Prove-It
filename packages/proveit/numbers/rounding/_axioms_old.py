from proveit.logic import Forall, Equals, And, InSet
from proveit.numbers import Floor, Sub, IntervalCO, Integer, Real
from proveit.common import x
from proveit.numbers.common import zero, one
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

floorDef = Forall(x, And(InSet(Floor(x), Integer), InSet(Sub(x, Floor(x)), IntervalCO(zero, one))), domain=Real)
floorDef

endAxioms(locals(), __package__)

