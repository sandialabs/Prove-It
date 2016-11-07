
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Exists, NotExists, Booleans, TRUE, FALSE, inBool, Not, And, Or, Implies, Iff, Equals, NotEquals
from proveit.common import A, B, C, P, Q, R, S, x, y, PofA, Qetc, Retc, xEtc, yEtc, zEtc, PxEtc, PyEtc, PxyEtc, etc_QxEtc, etc_QyEtc, etc_RyEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems


beginTheorems(locals())

trueEqTrue = Equals(TRUE, TRUE)
trueEqTrue

falseEqFalse = Equals(FALSE, FALSE)
falseEqFalse

trueConclusion = Forall(A, Implies(A, TRUE))
trueConclusion

selfImplication = Forall(A, Implies(A, A))
selfImplication

unfoldInBool = Forall(A, Implies(inBool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))
unfoldInBool

foldInBool = Forall(A, Implies(Or(Equals(A, TRUE), Equals(A, FALSE)), inBool(A)))
foldInBool

inBoolIfEqTrue = Forall(A, inBool(A), conditions=[Equals(A, TRUE)])

inBoolIfEqFalse = Forall(A, inBool(A), conditions=[Equals(A, FALSE)])

trueNotFalse = NotEquals(TRUE, FALSE)
trueNotFalse

notEqualsFalse = Forall(A, Implies(A, NotEquals(A, FALSE)))
notEqualsFalse

trueInBool = inBool(TRUE)
trueInBool

falseInBool = inBool(FALSE)
falseInBool

fromNotFalse = Forall(A, Implies(NotEquals(A, FALSE), A), domain=Booleans)
fromNotFalse

endTheorems(locals(), __package__)




