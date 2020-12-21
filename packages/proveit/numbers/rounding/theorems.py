from proveit.logic import Forall, InSet
from proveit.numbers import Integer, Natural, NaturalPos, Real, RealPos
from proveit.numbers import Round, Ceil, Floor
from proveit.common import a
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

round_real_closure = Forall(a, InSet(Round(a), Integer), domain=Real)
round_real_closure

round_real_pos_closure = Forall(a, InSet(Round(a), Natural), domain=RealPos)
round_real_pos_closure

ceil_real_closure = Forall(a, InSet(Ceil(a), Integer), domain=Real)
ceil_real_closure

ceil_real_pos_closure = Forall(a, InSet(Ceil(a), NaturalPos), domain=RealPos)
ceil_real_pos_closure

floor_real_closure = Forall(a, InSet(Floor(a), Integer), domain=Real)
floor_real_closure

floor_real_pos_closure = Forall(a, InSet(Floor(a), Natural), domain=RealPos)
floor_real_pos_closure

end_theorems(locals(), __package__)
