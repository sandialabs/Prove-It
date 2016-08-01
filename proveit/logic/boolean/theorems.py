
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Exists, NotExists, BOOLEANS, TRUE, FALSE, inBool, Not, And, Or, Implies, Iff, Equals, NotEquals
from proveit.common import A, B, C, P, Q, R, S, x, y, PofA, Qetc, Retc, xEtc, yEtc, zEtc, PxEtc, PyEtc, PxyEtc, etc_QxEtc, etc_QyEtc, etc_RyEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems


beginTheorems(locals())

trueEqTrue = Equals(TRUE, TRUE)
trueEqTrue

falseEqFalse = Equals(FALSE, FALSE)
falseEqFalse

eqTrueRevIntro = Forall(A, Implies(A, Equals(TRUE, A)))
eqTrueRevIntro

trueConclusion = Forall(A, Implies(A, TRUE))
trueConclusion

selfImplication = Forall(A, Implies(A, A))
selfImplication

unfoldInBool = Forall(A, Implies(inBool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))
unfoldInBool

foldInBool = Forall(A, Implies(Or(Equals(A, TRUE), Equals(A, FALSE)), inBool(A)))
foldInBool

trueNotFalse = NotEquals(TRUE, FALSE)
trueNotFalse

notEqualsFalse = Forall(A, Implies(A, NotEquals(A, FALSE)))
notEqualsFalse

trueInBool = inBool(TRUE)
trueInBool

falseInBool = inBool(FALSE)
falseInBool

fromNotFalse = Forall(A, Implies(NotEquals(A, FALSE), A), domain=BOOLEANS)
fromNotFalse

inBoolIfEqTrue = Forall(A, Implies(Equals(A, TRUE), inBool(A)))
inBoolIfEqTrue

inBoolIfEqTrueRev = Forall(A, Implies(Equals(TRUE, A), inBool(A)))
inBoolIfEqTrueRev

inBoolIfEqFalse = Forall(A, Implies(Equals(A, FALSE), inBool(A)))
inBoolIfEqFalse

inBoolIfEqFalseRev = Forall(A, Implies(Equals(FALSE, A), inBool(A)))
inBoolIfEqFalseRev

endTheorems(locals(), __package__)




