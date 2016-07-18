from proveit.logic import Or, TRUE, FALSE, Forall, Implies, Not, inBool, And, BOOLEANS
from proveit.common import A, B, C, y, xEtc, yEtc, zEtc
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

hypotheticalDisjunction = Forall((A, B, C), Implies(And(Implies(A, C), Implies(B, C)), Implies(Or(A, B), C)), domain=BOOLEANS)
hypotheticalDisjunction

disjunctionClosure = Forall((A, B), inBool(Or(A, B)), domain=BOOLEANS)
disjunctionClosure

orIfAny = Forall((xEtc, y, zEtc), Implies(y, Or(xEtc, y, zEtc)), domain=BOOLEANS)
orIfAny

endTheorems(locals(), __package__)
