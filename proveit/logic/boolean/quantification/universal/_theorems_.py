from proveit.logic import Forall, Implies, Booleans, And, Equals, TRUE, NotExists, Not, FALSE
from proveit.common import y, A, B, P, S, PofA, xMulti, yMulti, Qmulti, Rmulti, xEtc, yEtc, Qetc, Retc, PxEtc, PxyEtc, etc_RyEtc, etc_QxEtc
from proveit.logic.common import PofTrue, PofFalse
from proveit import beginTheorems, endTheorems, Operation

beginTheorems(locals())

unfoldForallOverBool = Forall(P, Implies(Forall(A, PofA, domain=Booleans), And(PofTrue, PofFalse)))
unfoldForallOverBool

foldForallOverBool = Forall(P, Implies(And(PofTrue, PofFalse), Forall(A, PofA, domain = Booleans)))
foldForallOverBool

forallBoolEvalTrue = Forall(P, Implies(And(PofTrue, PofFalse), Equals(Forall(A, PofA, domain=Booleans), TRUE)))
forallBoolEvalTrue

forallBundling = Forall((P, Qmulti, Rmulti, S), Implies(Forall(xMulti, Forall(yMulti, PxyEtc, S, etc_RyEtc), S, etc_QxEtc), Forall((xMulti, yMulti), PxyEtc, S, (etc_QxEtc, etc_RyEtc))))
forallBundling

forallUnraveling = Forall((P, Qmulti, Rmulti, S), Implies(Forall((xMulti, yMulti), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xMulti, Forall(yMulti, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))
forallUnraveling

forallBundledEquiv = Forall((P, Qmulti, Rmulti, S), Equals(Forall((xMulti, yMulti), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xMulti, Forall(yMulti, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))
forallBundledEquiv

forallEqTrueEquiv = Forall((P, Qmulti, S), Equals(Forall(xMulti, PxEtc, S, etc_QxEtc), Forall(xEtc, Equals(PxEtc, TRUE), S, etc_QxEtc)))
forallEqTrueEquiv

forallImpliesNotExistsNot = Forall((P, Qmulti, S), Implies(Forall(xMulti, PxEtc, S, etc_QxEtc), NotExists(xMulti, Not(PxEtc), S, etc_QxEtc)))
forallImpliesNotExistsNot

def _forallBoolEvalFalse(PofTrueVal, PofFalseVal):
    return Forall(P, Implies(And(Equals(PofTrue, PofTrueVal), Equals(PofFalse, PofFalseVal)), 
                             Equals(Forall(A, PofA, domain=Booleans), FALSE)))

forallBoolEvalFalseViaFF = _forallBoolEvalFalse(FALSE, FALSE)
forallBoolEvalFalseViaFF

forallBoolEvalFalseViaFT = _forallBoolEvalFalse(FALSE, TRUE)
forallBoolEvalFalseViaFT

forallBoolEvalFalseViaTF = _forallBoolEvalFalse(TRUE, FALSE)
forallBoolEvalFalseViaTF

# Forall_P {[P() and [Forall_{x*} P(x*) => Forall_{x*, y} P(x*, y)]] => Forall{x*} P(x*)}
forallInduction = Forall(P, Implies(And(Operation(P, []), 
                                    Implies(Forall(xMulti, PxEtc), 
                                            Forall((xMulti, y), Operation(P, [xEtc, y])))),
                                    Forall(xMulti, PxEtc)))

endTheorems(locals(), __package__)
