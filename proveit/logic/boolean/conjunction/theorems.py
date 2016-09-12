from proveit.logic import And, TRUE, Forall, inBool, Booleans
from proveit.common import Aetc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueAndTrue = And(TRUE, TRUE)
trueAndTrue

conjunctionIntro = Forall(Aetc, And(Aetc), conditions=[Aetc])
conjunctionIntro

conjunctionClosure = Forall(Aetc, inBool(And(Aetc)), domain=Booleans)
conjunctionClosure

endTheorems(locals(), __package__)
