from proveit.logic import Forall, Equals, And, Or, InSet, NotInSet, Intersect, Etcetera, Booleans
from proveit.common import A, B, Amulti, Aetc, x
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

membershipEval = Forall((x, Amulti), Equals(InSet(x, Intersect(Amulti)), And(Etcetera(InSet(x, Amulti)))))

binaryNonMembershipEval = Forall((x, A, B), Equals(NotInSet(x, Intersect(A, B)), Or(NotInSet(x, A), NotInSet(x, B))))

nonMembershipEval = Forall((x, Amulti), Equals(NotInSet(x, Intersect(Amulti)), Or(Etcetera(NotInSet(x, Amulti)))))

binaryMembershipFolding = Forall((x, A, B), InSet(x, Intersect(A, B)), conditions=[InSet(x, A), InSet(x, B)])

membershipFolding = Forall((x, Amulti), InSet(x, Intersect(Aetc)), conditions=[Etcetera(InSet(x, Amulti))])

binaryMembershipUnfolding = Forall((x, A, B), And(InSet(x, A), InSet(x, B)), conditions=[InSet(x, Intersect(A, B))])

membershipUnfolding = Forall((x, Amulti), And(Etcetera(InSet(x, Amulti))), conditions=[InSet(x, Intersect(Aetc))])

binaryNonmembershipFolding = Forall((x, A, B), NotInSet(x, Intersect(A, B)), conditions=[Or(NotInSet(x, A), NotInSet(InSet(x, B)))])

nonmembershipFolding = Forall((x, Amulti), NotInSet(x, Intersect(Amulti)), conditions=[Or(Etcetera(NotInSet(x, Amulti)))])

endTheorems(locals(), __package__)


