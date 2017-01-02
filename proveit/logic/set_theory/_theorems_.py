
# coding: utf-8

# In[1]:

from proveit.logic import Booleans, Forall, Exists, And, Or, Not, Implies, Iff, Equals, NotEquals, InSet, NotInSet, Singleton, Union, Intersect, Difference, SubsetEq, SupersetEq, SetOfAll
from proveit.common import f, x, y, A, B, C, S, P, fy, Px, Py, xEtc, yEtc, fxEtc, fyEtc, Qetc, etc_Qx, etc_Qy, etc_QyEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

notInSingleton = Forall((x, y), Equals(NotInSet(x, Singleton(y)), NotEquals(x, y)))
notInSingleton

endTheorems(locals(), __package__)


