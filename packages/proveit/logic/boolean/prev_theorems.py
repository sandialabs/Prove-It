
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

notEqualsFalse = Forall(A, NotEquals(A, FALSE), conditions=[A])

trueEqFalseEval = Equals(Equals(TRUE, FALSE), FALSE)

falseEqTrueEval = Equals(Equals(FALSE, TRUE), FALSE)

trueConclusion = Forall(A, Implies(A, TRUE))

inBoolEquiv = Forall(A, Equals(inBool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))

trueInBool = inBool(TRUE)

falseInBool = inBool(FALSE)

unfoldForallOverBool = Forall(P, Implies(Forall(A, PofA, domain=Booleans), And(PofTrue, PofFalse)))

inBoolIfTrue = Forall(A, inBool(A), conditions=[A])

inBoolIfFalse = Forall(A, inBool(A), conditions=[Not(A)])

# This weak form requires B to be a Boolean
byCasesWeak = Forall((A, B), B, domain=Booleans, conditions=[Implies(A, B), Implies(Not(A), B)])

# This is a stronger form that does not require B to be a Boolean
byCases = Forall(A, Forall(B, B, conditions=[Implies(A, B), Implies(Not(A), B)]), domain=Booleans)

foldForallOverBool = Forall(P, Forall(A, PofA, domain = Booleans), conditions=[PofTrue, PofFalse])

forallBoolEvalTrue = Forall(P, Equals(Forall(A, PofA, domain=Booleans), TRUE),  conditions=[PofTrue, PofFalse])

# uses constructive dilemma
unfoldInBool = Forall(A, Or(A, Not(A)), domain=Booleans)







fromNotFalse = Forall(A, A, domain=Booleans, conditions=[NotEquals(A, FALSE)])


notInBoolEquiv = Forall(A, Equals(inBool(A), And(NotEquals(A, TRUE), NotEquals(A, FALSE))))



endTheorems(locals(), __package__)




