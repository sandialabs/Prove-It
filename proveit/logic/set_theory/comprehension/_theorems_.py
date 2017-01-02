from proveit.logic import Forall, Exists, And, Implies, Equals, InSet, SubsetEq, SetOfAll
from proveit.common import f, x, y, S, yMulti, fyEtc, Q, Qx, Qy, Qmulti, Qetc, etc_Qx, etc_Qy, etc_QyEtc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

unfoldComprehension = Forall((S, Qmulti, f, x), Implies(InSet(x, SetOfAll(yMulti, fyEtc, domain=S, conditions=etc_QyEtc)), Exists(yMulti, Equals(x, fyEtc), domain=S, conditions=etc_QyEtc)))

foldComprehension = Forall((S, Qmulti, f, x), Implies(Exists(yMulti, Equals(x, fyEtc), domain=S, conditions=etc_QyEtc), InSet(x, SetOfAll(yMulti, fyEtc, domain=S, conditions=etc_QyEtc))))

basicComprehension = Forall((S, Qmulti, x), Equals(InSet(x, SetOfAll(y, y, domain=S, conditions=etc_Qy)), 
                                   And(InSet(x, y), etc_Qx)))

unfoldBasicComprehension = Forall((S, Qmulti), Forall(x, And(etc_Qx), domain=SetOfAll(y, y, domain=S, conditions=etc_Qy)))

unfoldBasic1CondComprehension = Forall((S, Q), Forall(x, Qx, domain=SetOfAll(y, y, domain=S, conditions=Qy)))

inSupersetIfInComprehension = Forall((S, Qmulti), Forall(x, InSet(x, S), domain=SetOfAll(y, y, domain=S, conditions=etc_Qy)))

comprehensionIsSubset = Forall((S, Qmulti), SubsetEq(SetOfAll(x, x, domain=S, conditions=etc_Qx), S))

foldBasicComprehension = Forall((S, Qmulti), Forall(x, InSet(x, SetOfAll(y, y, domain=S, conditions=etc_Qy)), domain=S, conditions=[etc_Qx]))

endTheorems(locals(), __package__)

