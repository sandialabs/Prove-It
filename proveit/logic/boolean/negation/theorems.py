from proveit.logic import Not, FALSE, Forall, Implies, Equals, TRUE, Or, NotEquals, Booleans, inBool
from proveit.common import A, B
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

notFalse = Not(FALSE)
notFalse

notImpliesEqFalse = Forall(A, Implies(Not(A), Equals(A, FALSE)))
notImpliesEqFalse

notImpliesEqFalseRev = Forall(A, Implies(Not(A), Equals(FALSE, A)))
notImpliesEqFalseRev

fromDoubleNegation = Forall(A, Implies(Not(Not(A)), A))
fromDoubleNegation

notTimpliesF = Implies(Not(TRUE), FALSE)
notTimpliesF

contradictionFromNegation = Forall(A, Implies(Not(A), Implies(A, FALSE)))
contradictionFromNegation

notFromEqFalse = Forall(A, Implies(Equals(A, FALSE), Not(A)))
notFromEqFalse

doubleNegation = Forall(A, Implies(A, Not(Not(A))))
doubleNegation

eqFalseFromNegation = Forall(A, Implies(A, Equals(Not(A), FALSE)))
eqFalseFromNegation

eqFalseRevFromNegation = Forall(A, Implies(A, Equals(FALSE, Not(A))))
eqFalseRevFromNegation

doubleNegationEquiv = Forall(A, Equals(A, Not(Not(A))), domain=Booleans)
doubleNegationEquiv

negationClosure = Forall(A, inBool(Not(A)), domain=Booleans)
negationClosure

hypotheticalContradiction = Forall(A, Implies(Implies(A, FALSE), Not(A)), domain=Booleans)
hypotheticalContradiction


endTheorems(locals(), __package__)
