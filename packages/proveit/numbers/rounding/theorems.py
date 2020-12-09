from proveit.logic import Forall, InSet
from proveit.numbers import Integer, Natural, NaturalPos, Real, RealPos
from proveit.numbers import Round, Ceil, Floor
from proveit.common import a
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

roundRealClosure = Forall(a, InSet(Round(a), Integer), domain=Real)
roundRealClosure

roundRealPosClosure = Forall(a, InSet(Round(a), Natural), domain=RealPos)
roundRealPosClosure

ceilRealClosure = Forall(a, InSet(Ceil(a), Integer), domain=Real)
ceilRealClosure

ceilRealPosClosure = Forall(a, InSet(Ceil(a), NaturalPos), domain=RealPos)
ceilRealPosClosure

floorRealClosure = Forall(a, InSet(Floor(a), Integer), domain=Real)
floorRealClosure

floorRealPosClosure = Forall(a, InSet(Floor(a), Natural), domain=RealPos)
floorRealPosClosure

endTheorems(locals(), __package__)
