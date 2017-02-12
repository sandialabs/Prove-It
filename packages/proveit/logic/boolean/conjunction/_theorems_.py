from proveit.logic import And, Not, TRUE, FALSE, Forall, inBool, Booleans, Equals
from proveit.common import A, B, Amulti, Bmulti, Cmulti, Dmulti, Emulti, Aetc, Betc, Cetc, Detc, Eetc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueAndTrue = And(TRUE, TRUE)

trueAndFalseNegated = Not(And(TRUE, FALSE))

falseAndTrueNegated = Not(And(FALSE, TRUE))

falseAndFalseNegated = Not(And(FALSE, FALSE))

andIfBoth = Forall((A, B), And(A, B), conditions=[A, B])

nandIfNotRight = Forall((A, B), Not(And(A, B)), conditions=[A, Not(B)])

nandIfNotLeft = Forall((A, B), Not(And(A, B)), conditions=[Not(A), B])

nandIfNeither = Forall((A, B), Not(And(A, B)), conditions=[Not(A), Not(B)])

falsifiedAndIfNotRight = Forall((A, B), Equals(And(A, B), FALSE), conditions=[A, Not(B)])

falsifiedAndIfNotLeft = Forall((A, B), Equals(And(A, B), FALSE), conditions=[Not(A), B])

falsifiedAndIfNeither = Forall((A, B), Equals(And(A, B), FALSE), conditions=[Not(A), Not(B)])



leftFromAnd = Forall((A, B), A, conditions=[And(A, B)])

rightFromAnd = Forall((A, B), B, conditions=[And(A, B)])

binaryCommutation = Forall((A, B), And(B, A), conditions=[And(A, B)])



eachInBool = Forall((Amulti, B, Cmulti), inBool(B), conditions=inBool(And(Aetc, B, Cetc)))

anyFromAnd = Forall((Amulti, B, Cmulti), B, conditions=[And(Aetc, B, Cetc)])
anyFromAnd


andIfAll = Forall(Amulti, And(Aetc), conditions=[Aetc])
andIfAll

andCommutation = Forall((Amulti, Bmulti, Cmulti, Dmulti, Emulti), And(Aetc, Betc, Cetc, Detc, Eetc), conditions=[And(Aetc, Detc, Cetc, Betc, Eetc)])

conjunctionTrueEval = Forall(Amulti, Equals(And(Aetc), TRUE), conditions=[Aetc])
conjunctionFalseEval = Forall((Amulti, Cmulti), Equals(And(Aetc, FALSE, Cetc), FALSE), domain=Booleans)

conjunctionClosure = Forall(Amulti, inBool(And(Aetc)), domain=Booleans)
conjunctionClosure

endTheorems(locals(), __package__)
