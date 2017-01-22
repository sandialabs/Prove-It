from proveit.logic import Forall, Iff, InSet, NotInSet, Difference, Singleton, And, Or, NotEquals, Equals
from proveit.common import x, y, S, A, B
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

nonMembershipEval = Forall((x, A, B), Equals(NotInSet(x, Difference(A, B)), Or(NotInSet(x, A), InSet(x, B))))

membershipFolding = Forall((x, A, B), InSet(x, Difference(A, B)), conditions=[InSet(x, A), NotInSet(x, B)])

membershipUnfolding = Forall((x, A, B), And(InSet(x, A), NotInSet(x, B)), conditions=[InSet(x, Difference(A, B))])

nonmembershipFolding = Forall((x, A, B), NotInSet(x, Difference(A, B)), conditions=[Or(NotInSet(x, A), InSet(x, B))])

inAllButOne = Forall((x, S, y), Iff(InSet(x, Difference(S, Singleton(y))), 
                                    And(InSet(x, S), NotEquals(x, y))))


endTheorems(locals(), __package__)


