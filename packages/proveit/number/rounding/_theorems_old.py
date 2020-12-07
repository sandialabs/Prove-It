from proveit.logic import Forall, InSet
from proveit.number import Integer, Natural, NaturalPos, Reals, RealsPos
from proveit.number import Round, Ceil, Floor
from proveit.common import a
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

roundRealClosure = Forall(a, InSet(Round(a), Integer), domain=Reals)
roundRealClosure

roundRealPosClosure = Forall(a, InSet(Round(a), Natural), domain=RealsPos)
roundRealPosClosure

ceilRealClosure = Forall(a, InSet(Ceil(a), Integer), domain=Reals)
ceilRealClosure

ceilRealPosClosure = Forall(a, InSet(Ceil(a), NaturalPos), domain=RealsPos)
ceilRealPosClosure

floorRealClosure = Forall(a, InSet(Floor(a), Integer), domain=Reals)
floorRealClosure

floorRealPosClosure = Forall(a, InSet(Floor(a), Natural), domain=RealsPos)
floorRealPosClosure

endTheorems(locals(), __package__)
