
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Exists, NotExists, Booleans, TRUE, FALSE, inBool, Not, And, Or, Implies, Iff, Equals, NotEquals
from proveit.common import A, B, C, P, Q, R, S, x, y, PofA, Qetc, Retc, xEtc, yEtc, zEtc, PxEtc, PyEtc, PxyEtc, etc_QxEtc, etc_QyEtc, etc_RyEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems


beginTheorems(locals())

trueEqTrue = Equals(TRUE, TRUE)

trueEqTrueEval = Equals(Equals(TRUE, TRUE), TRUE)

falseEqFalse = Equals(FALSE, FALSE)

falseEqFalseEval = Equals(Equals(FALSE, FALSE), TRUE)

trueNotFalse = NotEquals(TRUE, FALSE)

trueEqFalseEval = Equals(Equals(TRUE, FALSE), FALSE)

falseEqTrueEval = Equals(Equals(FALSE, TRUE), FALSE)

trueConclusion = Forall(A, Implies(A, TRUE))

inBoolEquiv = Forall(A, Equals(inBool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))

unfoldInBool = Forall(A, Or(Equals(A, TRUE), Equals(A, FALSE)), conditions=[inBool(A)])

trueInBool = inBool(TRUE)

falseInBool = inBool(FALSE)

inBoolIfTrue = Forall(A, inBool(A), conditions=[A])

inBoolIfFalse = Forall(A, inBool(A), conditions=[Not(A)])


notInBoolEquiv = Forall(A, Equals(inBool(A), And(NotEquals(A, TRUE), NotEquals(A, FALSE))))


notEqualsFalse = Forall(A, NotEquals(A, FALSE), conditions=[A])
notEqualsFalse

fromNotFalse = Forall(A, Implies(NotEquals(A, FALSE), A), domain=Booleans)
fromNotFalse

endTheorems(locals(), __package__)




