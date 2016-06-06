from proveit.logic import BOOLEANS, TRUE, FALSE, inBool, Forall, Exists, NotExists, And, Or, Not, Implies, Iff, \
Union, Singleton, Equals, NotEquals
from proveit.common import A, B, C, P, Q, S, x, Px, Qx, Aetc, Betc, Cetc, PxEtc, Qetc, xEtc, etc_QxEtc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

trueAxiom = TRUE
trueAxiom

boolsDef = Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE)))
boolsDef

boolsDef = Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE)))
boolsDef

boolsDef = Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE)))
boolsDef

falseNotTrue = NotEquals(FALSE, TRUE)
falseNotTrue

forallInBool = Forall((P, Qetc, S), inBool(Forall(xEtc, PxEtc, S, etc_QxEtc)))
forallInBool

existsDef = Forall((P, Qetc, S), Equals(Exists(xEtc, PxEtc, S, etc_QxEtc), Not(Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc))))
existsDef

notExistsDef = Forall((P, Qetc, S), Equals(NotExists(xEtc, PxEtc, S, etc_QxEtc), Not(Exists(xEtc, PxEtc, S, etc_QxEtc))))
notExistsDef

notF = Equals(Not(FALSE), TRUE)
notF

notT = Equals(Not(TRUE), FALSE)
notT

implicitNotF = Forall(A, Implies(Equals(Not(A), TRUE), Equals(A, FALSE)))
implicitNotF

implicitNotT = Forall(A, Implies(Equals(Not(A), FALSE), Equals(A, TRUE)))
implicitNotT

andTT = Equals(And(TRUE, TRUE), TRUE)
andTT

andTF = Equals(And(TRUE, FALSE), FALSE)
andTF

andFT = Equals(And(FALSE, TRUE), FALSE)
andFT

andFF = Equals(And(FALSE, FALSE), FALSE)
andFF

andComposition = Forall((A, Betc), Equals(And(A, Betc), And(A, And(Betc))))
andComposition

andImpliesEach = Forall((Aetc, B, Cetc), Implies(And(Aetc, B, Cetc), B))
andImpliesEach

orTT = Equals(Or(TRUE, TRUE), TRUE)
orTT

orTF = Equals(Or(TRUE, FALSE), TRUE)
orTF

orFT = Equals(Or(FALSE, TRUE), TRUE)
orFT

orFF = Equals(Or(FALSE, FALSE), FALSE)
orFF

orComposition = Forall((A, B, Cetc), Equals(Or(A, B, Cetc), Or(A, Or(B, Cetc))))
orComposition

iffDef = Forall((A, B), Equals(Iff(A, B), And(Implies(A, B), Implies(B, A))))
iffDef

eqTrueIntro = Forall(A, Implies(A, Equals(A, TRUE)))
eqTrueIntro

eqTrueElim = Forall(A, Implies(Equals(A, TRUE), A))
eqTrueElim

impliesTF = Equals(Implies(TRUE, FALSE), FALSE)
impliesTF

contradictoryValidation = Forall(A, Implies(Implies(Not(A), FALSE), A), domain=BOOLEANS)
contradictoryValidation

endAxioms(locals(), __package__)


