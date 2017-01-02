from proveit.logic import Forall, And, Equals, InSet, SetOfAll
from proveit.common import x, y, S, f, fx, fy, Qmulti, Qetc, etc_Qy, etc_Qx
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

# NOTE: Membership should only be defined for true sets and never on a universal domain.
# Otherwise, we could use set comprehension to build Russel's set.
comprehensionDef = Forall((S, Qmulti, f, x), Equals(InSet(fx, SetOfAll(y, fy, domain=S, conditions=etc_Qy)), 
                                   And(InSet(x, S), etc_Qx)))
                                   
endAxioms(locals(), __package__)
