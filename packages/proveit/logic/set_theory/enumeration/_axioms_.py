
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Equals, InSet, Set, Union
from proveit.common import x, y, xMulti, xEtc, z, A, B, C, S, f, P, fy, Py
from proveit import Etcetera
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

singletonDef = Forall((x, y), Equals(InSet(x, Set(y)), Equals(x, y)))
singletonDef

enumSetDef = Forall(xMulti, Equals(Set(xEtc), Union(Etcetera(Set(xMulti)))))
enumSetDef


# Is this prudent / necessary?
#setIsAsSetContains = Forall((A, B), Implies(Forall(x, Iff(InSet(x, A), InSet(x, B))), Equals(A, B)))
#setIsAsSetContains

endAxioms(locals(), __package__)



