from proveit.logic import Forall, InSet
from proveit.number import Integers, Naturals, NaturalsPos, Reals, RealsPos
from proveit.number import Round, Ceil, Floor
from proveit.common import a
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

roundRealClosure = Forall(a, InSet(Round(a), Integers), domain=Reals)
roundRealClosure

roundRealPosClosure = Forall(a, InSet(Round(a), Naturals), domain=RealsPos)
roundRealPosClosure

ceilRealClosure = Forall(a, InSet(Ceil(a), Integers), domain=Reals)
ceilRealClosure

ceilRealPosClosure = Forall(a, InSet(Ceil(a), NaturalsPos), domain=RealsPos)
ceilRealPosClosure

floorRealClosure = Forall(a, InSet(Floor(a), Integers), domain=Reals)
floorRealClosure

floorRealPosClosure = Forall(a, InSet(Floor(a), Naturals), domain=RealsPos)
floorRealPosClosure

endTheorems(locals(), __package__)
