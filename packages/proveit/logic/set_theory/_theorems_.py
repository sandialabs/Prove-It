
# coding: utf-8

# In[1]:

from proveit.logic import Booleans, TRUE, FALSE, Forall, Exists, And, Or, Not, Implies, Iff, Equals, NotEquals, InSet, NotInSet, Singleton, Union, Intersect, Difference, SubsetEq, SupersetEq, SetOfAll
from proveit.common import f, x, y, A, B, C, S, P, fy, Px, Py, xEtc, yEtc, fxEtc, fyEtc, Qetc, etc_Qx, etc_Qy, etc_QyEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


unfoldSingleton = Forall((x, y), Equals(x, y), conditions=[InSet(x, Singleton(y))])

foldSingleton = Forall((x, y), InSet(x, Singleton(y)), conditions=[Equals(x, y)])

nonMembershipEquiv = Forall((x, y), Equals(NotInSet(x, Singleton(y)), NotEquals(x, y)))

inSingletonIsBool = Forall((x, y), InSet(InSet(x, Singleton(y)), Booleans))
inSingletonEvalTrue = Forall((x, y), Equals(InSet(x, Singleton(y)), TRUE), conditions=[Equals(x, y)])
inSingletonEvalFalse = Forall((x, y), Equals(InSet(x, Singleton(y)), FALSE), conditions=[NotEquals(x, y)])
notInSingleton = Forall((x, y), Equals(NotInSet(x, Singleton(y)), NotEquals(x, y)))

endTheorems(locals(), __package__)


