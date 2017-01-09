
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Exists, And, Or, Not, Implies, Iff, Equals, InSet, NotInSet, Singleton, SetOfAll, Booleans, NOTHING
from proveit.common import x, y, z, A, B, C, S, f, P, fy, Py
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

singletonDef = Forall((x, y), Equals(InSet(x, Singleton(y)), Equals(x, y)))
singletonDef

# Is this prudent / necessary?
#setIsAsSetContains = Forall((A, B), Implies(Forall(x, Iff(InSet(x, A), InSet(x, B))), Equals(A, B)))
#setIsAsSetContains

endAxioms(locals(), __package__)



