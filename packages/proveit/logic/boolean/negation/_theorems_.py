from proveit.logic import Not, FALSE, Forall, Implies, Equals, TRUE, Or, NotEquals, Booleans, inBool
from proveit.common import A, B
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

notFalse = Not(FALSE)

# we derive these truth table theorems from stronger axioms
notF = Equals(Not(FALSE), TRUE)
notT = Equals(Not(TRUE), FALSE)

notTimpliesF = Implies(Not(TRUE), FALSE)

toDoubleNegation = Forall(A, Not(Not(A)), conditions=[A])

fromDoubleNegation = Forall(A, A, conditions=[Not(Not(A))])

negationContradiction = Forall(A, FALSE, conditions=[A, Not(A)])


closure = Forall(A, inBool(Not(A)), domain=Booleans)


negationForBooleansOnly = Forall(A, inBool(A), conditions=inBool(Not(A)))

doubleNegationEquiv = Forall(A, Equals(Not(Not(A)), A), domain=Booleans)




endTheorems(locals(), __package__)
