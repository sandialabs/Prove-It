from proveit.logic import Forall, Equals, And, InSet
from proveit.numbers import Floor, Sub, IntervalCO, Integer, Real
from proveit.common import x
from proveit.numbers.common import zero, one
from proveit import begin_axioms, end_axioms

begin_axioms(locals())

floor_def = Forall(x, And(InSet(Floor(x), Integer), InSet(
    Sub(x, Floor(x)), IntervalCO(zero, one))), domain=Real)
floor_def

end_axioms(locals(), __package__)
