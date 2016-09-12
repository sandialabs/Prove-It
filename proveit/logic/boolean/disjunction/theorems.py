from proveit.logic import Or, TRUE, FALSE, Forall, Implies, Not, inBool, And, Booleans
from proveit.common import A, B, C, Aetc, Cetc
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueOrTrue = Or(TRUE, TRUE)
trueOrTrue

trueOrFalse = Or(TRUE, FALSE)
trueOrFalse

falseOrTrue = Or(FALSE, TRUE)
falseOrTrue

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

disjunctionClosure = Forall(Aetc, inBool(Or(Aetc)), domain=Booleans)
disjunctionClosure

orIfAny = Forall((Aetc, B, Cetc), Implies(B, Or(Aetc, B, Cetc)), domain=Booleans)
orIfAny

endTheorems(locals(), __package__)
