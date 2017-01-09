from proveit.logic import Booleans, Forall, Exists, And, Or, Not, Implies, Iff, Equals, NotEquals, InSet, NotInSet, Singleton, Union, Intersect, Difference, SubsetEq, SupersetEq, SetOfAll
from proveit.common import f, x, y, A, B, C, S, P, fy, Px, Py, xEtc, yEtc, fxEtc, fyEtc, Qetc, etc_Qx, etc_Qy, etc_QyEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


foldNotIn = Forall((x, S), Implies(Not(InSet(x, S)), NotInSet(x, S)))
foldNotIn

unfoldNotIn = Forall((x, S), Implies(NotInSet(x, S), Not(InSet(x, S))))
unfoldNotIn

endTheorems(locals(), __package__)
