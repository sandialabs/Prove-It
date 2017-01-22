
# coding: utf-8

# In[1]:

from proveit.logic import Equals, NotEquals, Implies, Not, Forall, inBool
from proveit.common import x, y, z, f, fx, fy
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

equalityInBool = Forall((x, y), inBool(Equals(x, y)))

equalsTransitivity = Forall((x, y, z), Equals(x, z), conditions=[Equals(x, y), Equals(y, z)])

equalsReflexivity = Forall(x, Equals(x, x))

equalsSymmetry = Forall((x, y), Equals(Equals(y, x), Equals(x, y)))

notEqualsDef = Forall((x, y), Equals(NotEquals(x, y), Not(Equals(x, y))))

substitution = Forall((f, x, y), Equals(fx, fy), conditions=Equals(x, y))

endAxioms(locals(), __package__)

