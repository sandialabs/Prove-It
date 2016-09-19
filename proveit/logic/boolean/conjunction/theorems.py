from proveit.logic import And, TRUE, FALSE, Forall, inBool, Booleans, Equals
from proveit.common import Aetc, Cetc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueAndTrue = And(TRUE, TRUE)
trueAndTrue

conjunctionIntro = Forall(Aetc, And(Aetc), conditions=[Aetc])
conjunctionIntro

conjunctionTrueEval = Forall(Aetc, Equals(And(Aetc), TRUE), conditions=[Aetc])
conjunctionFalseEval = Forall((Aetc, Cetc), Equals(And(Aetc, FALSE, Cetc), FALSE), domain=Booleans)

conjunctionClosure = Forall(Aetc, inBool(And(Aetc)), domain=Booleans)
conjunctionClosure

endTheorems(locals(), __package__)
