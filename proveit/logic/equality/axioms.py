
# coding: utf-8

# In[1]:

from proveit.logic import Equals, NotEquals, Implies, Not, Forall, inBool
from proveit.common import x, y, z, f, fx, fy



# In[3]:

equalityInBool = Forall((x, y), inBool(Equals(x, y)))
equalityInBool


# In[4]:

equalsTransitivity = Forall((x, y, z), Implies(Equals(x, y), Implies(Equals(y, z), Equals(x, z))))
equalsTransitivity


# In[5]:

equalsReflexivity = Forall(x, Equals(x, x))
equalsReflexivity


# In[6]:

equalsSymmetry = Forall((x, y), Implies(Equals(x, y), Equals(y, x)))
equalsSymmetry


# In[7]:

notEqualsDef = Forall((x, y), Equals(NotEquals(x, y), Not(Equals(x, y))))
notEqualsDef


# In[8]:

substitution = Forall((f, x, y), Implies(Equals(x, y), Equals(fx, fy)))
substitution



