from proveit.logic import Forall, Equals, Or, And, InSet, NotInSet, Union, Booleans
from proveit.common import A, B, Amulti, Aetc, x
from proveit import Etcetera, beginTheorems, endTheorems

beginTheorems(locals())

binaryMembershipUnfolding = Forall((x, A, B), Or(InSet(x, A), InSet(x, B)), conditions=[InSet(x, Union(A, B))])

binaryMembershipFolding = Forall((x, A, B), InSet(x, Union(A, B)), conditions=[Or(InSet(x, A), InSet(x, B))])

binaryNonMembershipEquiv = Forall((x, A, B), Equals(NotInSet(x, Union(A, B)), And(NotInSet(x, A), NotInSet(x, B))))

binaryNonmembershipFolding = Forall((x, A, B), NotInSet(x, Union(A, B)), conditions=[NotInSet(x, A), NotInSet(x, B)])

membershipEquiv = Forall((x, Amulti), Equals(InSet(x, Union(Aetc)), Or(Etcetera(InSet(x, Amulti)))))

nonMembershipEquiv = Forall((x, Amulti), Equals(NotInSet(x, Union(Amulti)), And(Etcetera(NotInSet(x, Amulti)))))

membershipFolding = Forall((x, Amulti), InSet(x, Union(Aetc)), conditions=[Or(Etcetera(InSet(x, Amulti)))])

membershipUnfolding = Forall((x, Amulti), Or(Etcetera(InSet(x, Amulti))), conditions=[InSet(x, Union(Aetc))])

nonmembershipFolding = Forall((x, Amulti), NotInSet(x, Union(Aetc)), conditions=[Etcetera(NotInSet(x, Amulti))])

endTheorems(locals(), __package__)


