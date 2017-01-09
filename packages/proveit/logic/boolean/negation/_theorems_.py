from proveit.logic import Not, FALSE, Forall, Implies, Equals, TRUE, Or, NotEquals, Booleans, inBool
from proveit.common import A, B
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

notFalse = Not(FALSE)
notFalse

affirmViaFalseNegation = Forall(A, A, conditions=[Equals(Not(A), FALSE)])
affirmViaFalseNegation

denyViaTrueNegation = Forall(A, Not(A), conditions=[Equals(Not(A), TRUE)])
denyViaTrueNegation


eqFalseFromNot = Forall(A, Equals(A, FALSE), conditions=[Not(A)])
eqFalseFromNot

fromDoubleNegation = Forall(A, A, conditions=[Not(Not(A))])
fromDoubleNegation

notTimpliesF = Implies(Not(TRUE), FALSE)
notTimpliesF

contradictionViaNegation = Forall(A, FALSE, conditions=[A, Not(A)])
contradictionViaNegation

notFromEqFalse = Forall(A, Not(A), conditions=[Equals(A, FALSE)])
notFromEqFalse

doubleNegation = Forall(A, Not(Not(A)), conditions=[A])
doubleNegation

eqFalseFromNegation = Forall(A, Equals(Not(A), FALSE), conditions=[A])
eqFalseFromNegation

negationClosure = Forall(A, inBool(Not(A)), domain=Booleans)
negationClosure

doubleNegationEquiv = Forall(A, Equals(A, Not(Not(A))), domain=Booleans)
doubleNegationEquiv

hypotheticalContradiction = Forall(A, Implies(Implies(A, FALSE), Not(A)), domain=Booleans)
hypotheticalContradiction


endTheorems(locals(), __package__)
