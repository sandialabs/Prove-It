from proveit.logic import Forall, Implies, SubsetEq, SupersetEq, InSet, Equals
from proveit.common import A, B, x
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

unfoldSubsetEq = Forall((A, B), Implies(SubsetEq(A, B), Forall(x, InSet(x, B), A)))
unfoldSubsetEq

foldSubsetEq = Forall((A, B), Implies(Forall(x, InSet(x, B), A), SubsetEq(A, B)))
foldSubsetEq

unfoldSupersetEq = Forall((A, B), Implies(SupersetEq(A, B), Forall(x, InSet(x, A), B)))
unfoldSupersetEq

foldSupersetEq = Forall((A, B), Implies(Forall(x, InSet(x, A), B), SupersetEq(A, B)))
foldSupersetEq

subsetEqViaEquality = Forall((A, B), SubsetEq(A, B), conditions=[Equals(A, B)])

supersetEqViaEquality = Forall((A, B), SupersetEq(A, B), conditions=[Equals(A, B)])

endTheorems(locals(), __package__)


