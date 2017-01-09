from proveit.logic import And, Implies, TRUE, FALSE, Forall, inBool, Booleans, Equals
from proveit.common import A, B, Amulti, Cmulti, Aetc, Cetc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueAndTrue = And(TRUE, TRUE)
trueAndTrue

leftFromConjunction = Forall((A, B), A, conditions=[And(A, B)])
leftFromConjunction

rightFromConjunction = Forall((A, B), B, conditions=[And(A, B)])
rightFromConjunction

anyFromConjunction = Forall((Amulti, B, Cmulti), B, conditions=[And(Aetc, B, Cetc)])
anyFromConjunction

binaryConjunctionIntro = Forall((A, B), And(A, B), conditions=[A, B])
binaryConjunctionIntro

conjunctionIntro = Forall(Amulti, And(Aetc), conditions=[Aetc])
conjunctionIntro

conjunctionTrueEval = Forall(Amulti, Equals(And(Aetc), TRUE), conditions=[Aetc])
conjunctionFalseEval = Forall((Amulti, Cmulti), Equals(And(Aetc, FALSE, Cetc), FALSE), domain=Booleans)

conjunctionClosure = Forall(Amulti, inBool(And(Aetc)), domain=Booleans)
conjunctionClosure

endTheorems(locals(), __package__)
