from proveit.logic import Booleans, FALSE, Forall, Exists, And, Or, Not, Implies, Iff, Equals, NotEquals, InSet, NotInSet, Singleton, Union, Intersect, Difference, SubsetEq, SupersetEq, SetOfAll
from proveit.common import f, x, y, A, B, C, S, P, fy, Px, Py, xEtc, yEtc, fxEtc, fyEtc, Qetc, etc_Qx, etc_Qy, etc_QyEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


unfoldNotInSet = Forall((x, S), Not(InSet(x, S)), conditions=[NotInSet(x, S)])

foldNotInSet = Forall((x, S), NotInSet(x, S), conditions=[Not(InSet(x, S))])

endTheorems(locals(), __package__)
