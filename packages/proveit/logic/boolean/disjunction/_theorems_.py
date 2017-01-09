from proveit.logic import Or, TRUE, FALSE, Forall, Implies, Not, inBool, And, Booleans, Equals, Singleton
from proveit.common import A, B, C, Amulti, Cmulti, Aetc, Cetc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueOrTrue = Or(TRUE, TRUE)
trueOrTrue

trueOrFalse = Or(TRUE, FALSE)
trueOrFalse

falseOrTrue = Or(FALSE, TRUE)
falseOrTrue

orIfLeft = Forall((A, B), Or(A, B), domain=Booleans, conditions=[A])
orIfLeft

orIfRight = Forall((A, B), Or(A, B), domain=Booleans, conditions=[B])
orIfRight

orIfAny = Forall((Amulti, B, Cmulti), Or(Aetc, B, Cetc), domain=Booleans, conditions=[B])
orIfAny

disjunctionTrueEval = Forall((Amulti, Cmulti), Equals(Or(Aetc, TRUE, Cetc), TRUE), domain=Booleans)
disjunctionFalseEval = Forall(Amulti, Equals(Or(Aetc), FALSE), domain=Singleton(FALSE))

notOrFromNeither = Forall((A, B), Implies(Not(A), Implies(Not(B), Not(Or(A, B)))))
notOrFromNeither

orContradiction = Forall((A, B), Implies(Or(A, B), FALSE), conditions=(Not(A), Not(B)))
orContradiction

orImpliesLeftIfNotRight = Forall((A, B), Implies(Or(A, B), A), conditions=(inBool(A), Not(B)))
orImpliesLeftIfNotRight

orImpliesRightIfNotLeft = Forall((A, B), Implies(Or(A, B), B), conditions=(Not(A), inBool(B)))
orImpliesRightIfNotLeft

hypotheticalDisjunction = Forall((A, B, C), Implies(And(Implies(A, C), Implies(B, C)), Implies(Or(A, B), C)), domain=Booleans)
hypotheticalDisjunction

disjunctionBinaryClosure = Forall((A, B), inBool(Or(A, B)), domain=Booleans)
disjunctionBinaryClosure

disjunctionClosure = Forall(multiA, inBool(Or(Aetc)), domain=Booleans)
disjunctionClosure

endTheorems(locals(), __package__)
