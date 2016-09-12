from proveit.logic import Not, FALSE, Forall, Implies, Equals, TRUE, Or, NotEquals, Booleans, inBool
from proveit.common import A, B
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

notFalse = Not(FALSE)
notFalse

eqFalseFromNot = Forall(A, Equals(A, FALSE), conditions=[Not(A)])
eqFalseFromNot

fromDoubleNegation = Forall(A, A, conditions=[Not(Not(A))])
fromDoubleNegation

notTimpliesF = Implies(Not(TRUE), FALSE)
notTimpliesF

contradictionFromNegation = Forall(A, Implies(Not(A), Implies(A, FALSE)))
contradictionFromNegation

notFromEqFalse = Forall(A, Not(A), conditions=[Equals(A, FALSE)])
notFromEqFalse

doubleNegation = Forall(A, Not(Not(A)), conditions=[A])
doubleNegation

eqFalseFromNegation = Forall(A, Equals(Not(A), FALSE), conditions=[A])
eqFalseFromNegation

doubleNegationEquiv = Forall(A, Equals(A, Not(Not(A))), domain=Booleans)
doubleNegationEquiv

negationClosure = Forall(A, inBool(Not(A)), domain=Booleans)
negationClosure

hypotheticalContradiction = Forall(A, Implies(Implies(A, FALSE), Not(A)), domain=Booleans)
hypotheticalContradiction


endTheorems(locals(), __package__)
