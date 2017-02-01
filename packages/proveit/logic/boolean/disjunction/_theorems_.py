from proveit.logic import Or, TRUE, FALSE, Forall, Implies, Not, inBool, And, Booleans, Equals, Singleton
from proveit.common import A, B, C, D, Amulti, Cmulti, Aetc, Cetc
from proveit import Etcetera
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueOrTrue = Or(TRUE, TRUE)

trueOrFalse = Or(TRUE, FALSE)

falseOrTrue = Or(FALSE, TRUE)

falseOrFalseNegated = Not(Or(FALSE, FALSE))

orIfBoth = Forall((A, B), Or(A, B), conditions=[A, B])

orIfOnlyLeft = Forall((A, B), Or(A, B), conditions=[A, Not(B)])

orIfOnlyRight = Forall((A, B), Or(A, B), conditions=[Not(A), B])

notOrFromNeither = Forall((A, B), Not(Or(A, B)), conditions=[Not(A), Not(B)])

binaryOrContradiction = Forall((A, B), FALSE, conditions=(Or(A, B), Not(A), Not(B)))

leftIfNotRight = Forall((A, B), A, domain=Booleans, conditions=(Or(A, B), Not(B)))

rightIfNotLeft = Forall((A, B), B, domain=Booleans, conditions=(Or(A, B), Not(A)))

disjunctiveAffirmation = Forall((A, B, C), C, domain=Booleans, conditions=[Or(A, B), Implies(A, C), Implies(B, C)])

constructiveDilemma = Forall((A, B, C, D), Or(C, D), domain=Booleans, conditions=[Or(A, B), Implies(A, C), Implies(B, D)])


orIfLeft = Forall((A, B), Or(A, B), domain=Booleans, conditions=[A])

orIfRight = Forall((A, B), Or(A, B), domain=Booleans, conditions=[B])


orIfAny = Forall((Amulti, B, Cmulti), Or(Aetc, B, Cetc), domain=Booleans, conditions=[B])

notOrIfNotAny = Forall((Amulti), Not(Or(Aetc)), domain=Booleans, conditions=[Etcetera(Not(Amulti))])

orContradiction = Forall(Amulti, FALSE, conditions=(Or(Amulti), Etcetera(Not(Amulti))))

disjunctionTrueEval = Forall((Amulti, Cmulti), Equals(Or(Aetc, TRUE, Cetc), TRUE), domain=Booleans)
disjunctionFalseEval = Forall(Amulti, Equals(Or(Aetc), FALSE), domain=Singleton(FALSE))



binaryClosure = Forall((A, B), inBool(Or(A, B)), domain=Booleans)

closure = Forall(Amulti, inBool(Or(Aetc)), domain=Booleans)

endTheorems(locals(), __package__)
