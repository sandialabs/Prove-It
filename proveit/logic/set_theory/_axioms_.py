
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Exists, And, Or, Not, Implies, Iff, Equals, InSet, NotInSet, Singleton, SetOfAll, NOTHING
from proveit.common import x, y, z, A, B, C, S, f, P, fy, Py
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

notInDef = Forall((x, S), Equals(NotInSet(x, S), Not(InSet(x, S))))
notInDef

singletonDef = Forall((x, y), Equals(InSet(x, Singleton(y)), Equals(x, y)))
singletonDef

setOfAllDef = Forall((P, f, x), Iff(InSet(x, SetOfAll(y, fy, conditions=Py)), Exists(y, Equals(x, fy), conditions=Py)))
setOfAllDef

setIsAsSetContains = Forall((A, B), Implies(Forall(x, Iff(InSet(x, A), InSet(x, B))), Equals(A, B)))
setIsAsSetContains

allNotInNothing = Forall(x, NotInSet(x, NOTHING))
allNotInNothing

endAxioms(locals(), __package__)



