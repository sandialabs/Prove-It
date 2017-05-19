
# coding: utf-8

# In[1]:

from proveit import Etcetera
from proveit.logic import Booleans, TRUE, FALSE, Forall, Or,  Equals, NotEquals, InSet, NotInSet, Singleton, Set
from proveit.common import f, x, y, yMulti, yEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())


unfoldSingleton = Forall((x, y), Equals(x, y), conditions=[InSet(x, Set(y))])

foldSingleton = Forall((x, y), InSet(x, Set(y)), conditions=[Equals(x, y)])

notInSingletonEquiv = Forall((x, y), Equals(NotInSet(x, Set(y)), NotEquals(x, y)))

inSingletonIsBool = Forall((x, y), InSet(InSet(x, Set(y)), Booleans))
inSingletonEvalTrue = Forall((x, y), Equals(InSet(x, Set(y)), TRUE), conditions=[Equals(x, y)])
inSingletonEvalFalse = Forall((x, y), Equals(InSet(x, Set(y)), FALSE), conditions=[NotEquals(x, y)])
notInSingleton = Forall((x, y), Equals(NotInSet(x, Set(y)), NotEquals(x, y)))

membershipEquiv = Forall((x, yMulti), Equals(InSet(x, Set(yEtc)), Or(Etcetera(Equals(x, yMulti)))))
membershipEquiv

unfold = Forall((x, yMulti), Or(Etcetera(Equals(x, yMulti)), conditions=[InSet(x, Set(yEtc))])

fold = Forall((x, yMulti), InSet(x, Set(yEtc)), conditions=[Or(Etcetera(Equals(x, yMulti)))])

nonMembershipEquiv = Forall((x, yMulti), Equals(NotInSet(x, Set(yEtc)), And(Etcetera(NotEquals(x, yMulti)))))
nonMembershipEquiv

endTheorems(locals(), __package__)


