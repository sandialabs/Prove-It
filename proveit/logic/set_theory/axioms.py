
# coding: utf-8

# In[1]:

from proveit.logic import BOOLEANS, Forall, Exists, And, Or, Not, Implies, Iff, Equals, InSet, NotInSet, Singleton, Union, Intersection, Difference, SubsetEq, SupersetEq, SetOfAll, NOTHING
from proveit.common import x, y, z, A, B, C, Cetc, S, f, P, fy, Py
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

# In[3]:

notInDef = Forall((x, S), Equals(NotInSet(x, S), Not(InSet(x, S))))
notInDef


# In[4]:

singletonDef = Forall((x, y), Equals(InSet(x, Singleton(y)), Equals(x, y)))
singletonDef


# In[5]:

unionDef = Forall((x, A, B), Iff(InSet(x, Union(A, B)), Or(InSet(x, A), InSet(x, B))))
unionDef


# In[6]:

intersectionDef = Forall((x, A, B), Iff(InSet(x, Intersection(A, B)), And(InSet(x, A), InSet(x, B))))
intersectionDef


# In[7]:

unionComposition = Forall((A, B, Cetc), Equals(Union(A, B, Cetc), Union(A, Union(B, Cetc))))
unionComposition


# In[8]:

intersectionComposition = Forall((A, B, Cetc), Equals(Intersection(A, B, Cetc), Intersection(A, Intersection(B, Cetc))))
intersectionComposition


# In[9]:

differenceDef = Forall((x, A, B), Iff(InSet(x, Difference(A, B)), 
                                      And(InSet(x, A), NotInSet(x, B))))
differenceDef


# In[10]:

subsetDef = Forall((A, B), Iff(SubsetEq(A, B), Forall(x, InSet(x, B), A)))
subsetDef


# In[11]:

supersetDef = Forall((A, B), Iff(SupersetEq(A, B), Forall(x, InSet(x, A), B)))
supersetDef


# In[12]:

setOfAllDef = Forall((P, f, x), Iff(InSet(x, SetOfAll(y, fy, conditions=Py)), Exists(y, Equals(x, fy), conditions=Py)))
setOfAllDef


# In[13]:

setIsAsSetContains = Forall((A, B), Implies(Forall(x, Iff(InSet(x, A), InSet(x, B))), Equals(A, B)))
setIsAsSetContains


# In[15]:

allNotInNothing = Forall(x, NotInSet(x, NOTHING))
allNotInNothing

endAxioms(locals(), __package__)



