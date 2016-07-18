from proveit.logic import Forall, Iff, InSet, Difference, Singleton, And, NotEquals
from proveit.common import x, y, S
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


inAllButOne = Forall((x, S, y), Iff(InSet(x, Difference(S, Singleton(y))), 
                                    And(InSet(x, S), NotEquals(x, y))))
inAllButOne


endTheorems(locals(), __package__)


