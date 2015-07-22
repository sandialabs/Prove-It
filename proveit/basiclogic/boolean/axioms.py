from proveit.statement import Axioms
from proveit.expression import Operation
from proveit.multiExpression import Etcetera
from boolSet import BOOLEANS, TRUE, FALSE, inBool
from quantifiers import Forall, Exists, NotExists
from boolOps import And, Or, Not, Implies, Iff
from proveit.basiclogic import Union, Singleton, Equals, NotEquals
from proveit.basiclogic.variables import A, B, C, P, Q, S, x
from proveit.basiclogic.simpleExpr import Px, Qx, etcA, etcC, PxEtc, etcQ, xEtc, etc_QxEtc
import sys

booleanAxioms = Axioms(__package__, locals())

# TRUE
trueAxiom = TRUE

# BOOLEANS = {TRUE} union {FALSE}
boolsDef = Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE)))
    
# FALSE != TRUE
falseNotTrue = NotEquals(FALSE, TRUE)
    
# Forall statements are in the BOOLEAN set.  If it isn't TRUE, then it is FALSE.
# forall_{P, ..Q.., S} [forall_{..x.. in S | ..Q(..x..)..} P(..x..)] in BOOLEANS
forallInBool = Forall((P, etcQ, S), inBool(Forall(xEtc, PxEtc, S, etc_QxEtc)))

# If it's ever true, it can't always be not true.  (example exists = not never)
# forall_{P, ..Q.., S} [exists_{..x.. in S | ..Q(..x..)..} P(..x..) = not[forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)]]
existsDef = Forall((P, etcQ, S), Equals(Exists(xEtc, PxEtc, S, etc_QxEtc), Not(Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc))))

# forall_{P, ..Q.., S} notexists_{..x.. in S | ..Q(..x..)..} P(..x..) = not[exists_{..x.. in S | ..Q(..x..)..} P(..x..)]
notExistsDef = Forall((P, etcQ, S), Equals(NotExists(xEtc, PxEtc, S, etc_QxEtc), Not(Exists(xEtc, PxEtc, S, etc_QxEtc))))

# Truth table for NOT
notF = Equals(Not(FALSE), TRUE)
notT = Equals(Not(TRUE), FALSE)

# Further defining property of NOT needed in addition to the truth table
# because the truth table is ambiguous regarding inputs neither TRUE nor FALSE.

# forall_{A} [Not(A) = TRUE] => [A=FALSE]
implicitNotF = Forall(A, Implies(Equals(Not(A), TRUE), Equals(A, FALSE)))
# forall_{A} [Not(A) = FALSE] => [A=TRUE]
implicitNotT = Forall(A, Implies(Equals(Not(A), FALSE), Equals(A, TRUE)))


# Truth table for AND
andTT = Equals(And(TRUE, TRUE), TRUE)
andTF = Equals(And(TRUE, FALSE), FALSE)
andFT = Equals(And(FALSE, TRUE), FALSE)
andFF = Equals(And(FALSE, FALSE), FALSE)

# Composition of multi-And, bypassing associativity for notational convenience:
# forall_{A, B, ..C..} A and B and ..C.. = A and (B and ..C..)
andComposition = Forall((A, B, etcC), Equals(And(A, B, etcC), And(A, And(B, etcC))))

# A further defining property of AND is needed in addition to the truth table
# because the truth table is ambiguous if we don't know that inputs are TRUE or FALSE:        
# forall_{..A.., B, ..C..} ..A.. and B and ..C.. => B
andImpliesEach = Forall((etcA, B, etcC), Implies(And(etcA, B, etcC), B))

# Truth table for OR
orTT = Equals(Or(TRUE, TRUE), TRUE)
orTF = Equals(Or(TRUE, FALSE), TRUE)
orFT = Equals(Or(FALSE, TRUE), TRUE)
orFF = Equals(Or(FALSE, FALSE), FALSE)

# Composition of multi-Or, bypassing associativity for notational convenience:
# forall_{A, B, ..C..} A or B or ..C.. = A or (B or ..C..)
orComposition = Forall((A, B, etcC), Equals(Or(A, B, etcC), Or(A, Or(B, etcC))))

# forall_{A, B} (A <=> B) = [(A => B) and (B => A)]
iffDef = Forall((A, B), Equals(Iff(A, B), And(Implies(A, B), Implies(B, A))))

# forall_{A} A => (A = TRUE)
eqTrueIntro = Forall(A, Implies(A, Equals(A, TRUE)))
# forall_{A} (A = TRUE) => A
eqTrueElim = Forall(A, Implies(Equals(A, TRUE), A))

# (TRUE => FALSE) = FALSE
impliesTF = Equals(Implies(TRUE, FALSE), FALSE)

# forall_{A in BOOLEANS} [Not(A) => FALSE] => A
contradictoryValidation = Forall(A, Implies(Implies(Not(A), FALSE), A), domain=BOOLEANS)

booleanAxioms.finish(locals())
