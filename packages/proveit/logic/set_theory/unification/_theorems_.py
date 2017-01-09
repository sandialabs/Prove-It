from proveit.logic import Forall, Equals, Or, Not, InSet, Union, Booleans, TRUE, FALSE
from proveit.common import A, B, Cmulti, Cetc, x
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

unionFolding = Forall((x, A, B), InSet(x, Union(A, B)), conditions=[Or(InSet(x, A), InSet(x, B))])
unionFolding

unionUnfolding = Forall((x, A, B), Or(InSet(x, A), InSet(x, B)), conditions=[InSet(x, Union(A, B))])
unionUnfolding

unionEvalFalse = Forall((x, A, B), Equals(InSet(x, Union(A, B)), FALSE), conditions=[Not(InSet(x, A)), Not(InSet(x, B))])
unionEvalFalse

unionEvalViaInLeft = Forall((x, A, B), Equals(InSet(x, Union(A, B)), FALSE), conditions=[InSet(x, A), InSet(InSet(x, B), Booleans)])
unionEvalViaInLeft

unionEvalViaInRight = Forall((x, A, B), Equals(InSet(x, Union(A, B)), FALSE), conditions=[InSet(x, B), InSet(InSet(x, A), Booleans)])
unionEvalViaInRight

endTheorems(locals(), __package__)


