
# coding: utf-8

# In[1]:

from proveit.logic import BOOLEANS, Forall, Exists, And, Or, Not, Implies, Iff, Equals, NotEquals, InSet, NotInSet, Singleton, Union, Intersection, Difference, SubsetEq, SupersetEq, SetOfAll
from proveit.common import f, x, y, A, B, C, S, P, fy, Px, Py, yEtc, fyEtc, Qetc, etc_QyEtc


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

inAllButOne = Forall((x, S, y), Iff(InSet(x, Difference(S, Singleton(y))), 
                                    And(InSet(x, S), NotEquals(x, y))))
inAllButOne


# In[7]:

unfoldSubsetEq = Forall((A, B), Implies(SubsetEq(A, B), Forall(x, InSet(x, B), A)))
unfoldSubsetEq


# In[8]:

foldSubsetEq = Forall((A, B), Implies(Forall(x, InSet(x, B), A), SubsetEq(A, B)))
foldSubsetEq


# In[9]:

unfoldSupersetEq = Forall((A, B), Implies(SupersetEq(A, B), Forall(x, InSet(x, A), B)))
unfoldSupersetEq


# In[10]:

foldSupersetEq = Forall((A, B), Implies(Forall(x, InSet(x, A), B), SupersetEq(A, B)))
foldSupersetEq


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



# In[ ]:




# In[ ]:



