
# coding: utf-8

# In[1]:

from proveit.logic import BOOLEANS, Forall, Exists, And, Or, Not, Implies, Iff, Equals, NotEquals, InSet, NotInSet, Singleton, Union, Intersect, Difference, SubsetEq, SupersetEq, SetOfAll
from proveit.common import f, x, y, A, B, C, S, P, fy, Px, Py, yEtc, fyEtc, Qetc, etc_QyEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

# In[3]:

foldNotIn = Forall((x, S), Implies(Not(InSet(x, S)), NotInSet(x, S)))
foldNotIn


# In[4]:

unfoldNotIn = Forall((x, S), Implies(NotInSet(x, S), Not(InSet(x, S))))
unfoldNotIn


# In[5]:

notInSingleton = Forall((x, y), Equals(NotInSet(x, Singleton(y)), NotEquals(x, y)))
notInSingleton


# In[6]:

# In[7]:


# In[11]:

unfoldSetOfAll = Forall((Qetc, f, x), Implies(InSet(x, SetOfAll(yEtc, fyEtc, conditions=etc_QyEtc)), Exists(yEtc, Equals(x, fyEtc), conditions=etc_QyEtc)))
unfoldSetOfAll


# In[12]:

foldSetOfAll = Forall((Qetc, f, x), Implies(Exists(yEtc, Equals(x, fyEtc), conditions=etc_QyEtc), InSet(x, SetOfAll(yEtc, fyEtc, conditions=etc_QyEtc))))
foldSetOfAll


# In[13]:

unfoldSimpleSetOfAll = Forall((P, x), Implies(InSet(x, SetOfAll(y, y, conditions=Py)), Px))
unfoldSimpleSetOfAll


# In[14]:

foldSimpleSetOfAll = Forall((P, x), Implies(Px, InSet(x, SetOfAll(y, y, conditions=Py))))
foldSimpleSetOfAll


endTheorems(locals(), __package__)


