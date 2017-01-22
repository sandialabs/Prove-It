from proveit.logic import Not, FALSE, Forall, Implies, Equals, TRUE, Or, NotEquals, Booleans, inBool
from proveit.common import A, B
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

notFalse = Not(FALSE)

# we derive these truth table theorems from stronger axioms
notF = Equals(Not(FALSE), TRUE)
notT = Equals(Not(TRUE), FALSE)

notTimpliesF = Implies(Not(TRUE), FALSE)

doubleNegation = Forall(A, Not(Not(A)), conditions=[A])

fromDoubleNegation = Forall(A, A, conditions=[Not(Not(A))])

contradictionViaNegation = Forall(A, FALSE, conditions=[A, Not(A)])

closure = Forall(A, inBool(Not(A)), domain=Booleans)


negationForBooleansOnly = Forall(A, inBool(A), conditions=inBool(Not(A)))






doubleNegationEquiv = Forall(A, Equals(A, Not(Not(A))), domain=Booleans)

hypotheticalContradiction = Forall(A, Implies(Implies(A, FALSE), Not(A)), domain=Booleans)


endTheorems(locals(), __package__)
