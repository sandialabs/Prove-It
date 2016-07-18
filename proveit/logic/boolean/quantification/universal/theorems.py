from proveit.logic import Forall, Implies, BOOLEANS, And, Equals, TRUE, NotExists, Not, FALSE
from proveit.common import A, B, P, S, PofA, xEtc, yEtc, Qetc, Retc, PxEtc, PxyEtc, etc_RyEtc, etc_QxEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

unfoldForallOverBool = Forall(P, Implies(Forall(A, PofA, domain=BOOLEANS), And(PofTrue, PofFalse)))
unfoldForallOverBool

foldForallOverBool = Forall(P, Implies(And(PofTrue, PofFalse), Forall(A, PofA, domain = BOOLEANS)))
foldForallOverBool

forallBoolEvalTrue = Forall(P, Implies(And(PofTrue, PofFalse), Equals(Forall(A, PofA, domain=BOOLEANS), TRUE)))
forallBoolEvalTrue

forallBundling = Forall((P, Qetc, Retc, S), Implies(Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc), Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc))))
forallBundling

forallUnraveling = Forall((P, Qetc, Retc, S), Implies(Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))
forallUnraveling

forallBundledEquiv = Forall((P, Qetc, Retc, S), Equals(Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))
forallBundledEquiv

forallEqTrueEquiv = Forall((P, Qetc, S), Equals(Forall(xEtc, PxEtc, S, etc_QxEtc), Forall(xEtc, Equals(PxEtc, TRUE), S, etc_QxEtc)))
forallEqTrueEquiv

forallImpliesNotExistsNot = Forall((P, Qetc, S), Implies(Forall(xEtc, PxEtc, S, etc_QxEtc), NotExists(xEtc, Not(PxEtc), S, etc_QxEtc)))
forallImpliesNotExistsNot

def _forallBoolEvalFalse(PofTrueVal, PofFalseVal):
    return Forall(P, Implies(And(Equals(PofTrue, PofTrueVal), Equals(PofFalse, PofFalseVal)), 
                             Equals(Forall(A, PofA, domain=BOOLEANS), FALSE)))

forallBoolEvalFalseViaFF = _forallBoolEvalFalse(FALSE, FALSE)
forallBoolEvalFalseViaFF

forallBoolEvalFalseViaFT = _forallBoolEvalFalse(FALSE, TRUE)
forallBoolEvalFalseViaFT

forallBoolEvalFalseViaTF = _forallBoolEvalFalse(TRUE, FALSE)
forallBoolEvalFalseViaTF

endTheorems(locals(), __package__)
