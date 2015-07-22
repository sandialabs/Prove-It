from proveit.statement import Theorems
from proveit.expression import Operation
from quantifiers import Forall, Exists, NotExists
from boolSet import BOOLEANS, TRUE, FALSE, inBool
from boolOps import Not, And, Or, Implies, Iff
from proveit.basiclogic import Equals, NotEquals
from proveit.basiclogic.variables import A, B, C, P, Q, R, S, x, y
from proveit.basiclogic.simpleExpr import PofA, PofTrue, PofFalse, Px, Py, Pxy, Qx, Ry, etcQ, etcR, xEtc, yEtc, PxEtc, PyEtc, PxyEtc, etc_QxEtc, etc_QyEtc, etc_RyEtc

booleanTheorems = Theorems(__package__, locals())

# Not(FALSE)
notFalse = Not(FALSE)

# TRUE and TRUE
trueAndTrue = And(TRUE, TRUE)

# TRUE or TRUE
trueOrTrue = Or(TRUE, TRUE)

# TRUE or FALSE
trueOrFalse = Or(TRUE, FALSE)

# FALSE or TRUE
falseOrTrue = Or(FALSE, TRUE)

# TRUE = TRUE
trueEqTrue = Equals(TRUE, TRUE)

# FALSE = FALSE
falseEqFalse = Equals(FALSE, FALSE)

# forall_{A} A => (TRUE = A)
eqTrueRevIntro = Forall(A, Implies(A, Equals(TRUE, A)))

# forall_{A} (TRUE = A) => A
eqTrueRevElim = Forall(A, Implies(Equals(TRUE, A), A))

# forall_{A} Not(A) => [A=FALSE]
notImpliesEqFalse = Forall(A, Implies(Not(A), Equals(A, FALSE)))

# forall_{A} Not(A) => (FALSE = A)
notImpliesEqFalseRev = Forall(A, Implies(Not(A), Equals(FALSE, A)))

# forall_{A} Not(Not(A)) => A
fromDoubleNegation = Forall(A, Implies(Not(Not(A)), A))

# forall_{A} A => TRUE
trueConclusion = Forall(A, Implies(A, TRUE))

# forall_{A} A => A, by a trivial hypothetical reasoning
selfImplication = Forall(A, Implies(A, A))

# (TRUE => TRUE) = TRUE
impliesTT = Equals(Implies(TRUE, TRUE), TRUE)

# (FALSE => TRUE) = TRUE
impliesFT = Equals(Implies(FALSE, TRUE), TRUE)

# (FALSE => FALSE) = TRUE
impliesFF = Equals(Implies(FALSE, FALSE), TRUE)

# (TRUE <=> TRUE) = TRUE
iffTT = Equals(Iff(TRUE, TRUE), TRUE)

# (FALSE <=> FALSE) = TRUE
iffFF = Equals(Iff(FALSE, FALSE), TRUE)

# (TRUE <=> FALSE) = FALSE
iffTF = Equals(Iff(TRUE, FALSE), FALSE)

# (FALSE <=> TRUE) = FALSE
iffFT = Equals(Iff(FALSE, TRUE), FALSE)

# forall_{A, B} (A <=> B) => (A => B)
iffImpliesRight = Forall((A, B), Implies(Iff(A, B), Implies(A, B)))

# forall_{A, B} (A <=> B) => (B => A)
iffImpliesLeft = Forall((A, B), Implies(Iff(A, B), Implies(B, A)))

# forall_{A, B} (A <=> B) => (B <=> A)
iffSymmetry = Forall((A, B), Implies(Iff(A, B), Iff(B, A)))

# forall_{A, B, C} (A <=> B and B <=> C) => (A <=> C)
iffTransitivity = Forall((A, B, C), Implies(And(Iff(A, B), Iff(B, C)), Iff(A, C)))

# Not(TRUE) => FALSE
notTimpliesF = Implies(Not(TRUE), FALSE)

# forall_{A, B | A, B} (A and B)
conjunctionIntro = Forall((A, B), And(A, B), conditions=(A, B))

# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
unfoldInBool = Forall(A, Implies(inBool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))

# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
foldInBool = Forall(A, Implies(Or(Equals(A, TRUE), Equals(A, FALSE)), inBool(A)))

# forall_{A} Not(A) => [A => FALSE]
contradictionFromNegation = Forall(A, Implies(Not(A), Implies(A, FALSE)))

# forall_{A} (A=FALSE) => Not(A)
notFromEqFalse = Forall(A, Implies(Equals(A, FALSE), Not(A)))

# forall_{A} (FALSE=A) => Not(A)
notFromEqFalseRev = Forall(A, Implies(Equals(FALSE, A), Not(A)))

# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
notOrFromNeither = Forall((A, B), Implies(Not(A), Implies(Not(B), Not(Or(A, B)))))

# forall_{A, B | Not(A), Not(B)} (A or B) => FALSE
orContradiction = Forall((A, B), Implies(Or(A, B), FALSE), conditions=(Not(A), Not(B)))

# forall_{A, B | inBool(A), Not(B)} (A or B) => A
orImpliesLeftIfNotRight = Forall((A, B), Implies(Or(A, B), A), conditions=(inBool(A), Not(B)))

# forall_{A, B | Not(A), inBool(B)} (A or B) => B
orImpliesRightIfNotLeft = Forall((A, B), Implies(Or(A, B), B), conditions=(Not(A), inBool(B)))

# forall_{A} A => Not(Not(A))
doubleNegation = Forall(A, Implies(A, Not(Not(A))))

# forall_{A} A => [Not(A)=FALSE]
eqFalseFromNegation = Forall(A, Implies(A, Equals(Not(A), FALSE)))

# forall_{A} A => [FALSE=Not(A)]
eqFalseRevFromNegation = Forall(A, Implies(A, Equals(FALSE, Not(A))))

# forall_{A in BOOLEANS} (A != FALSE) => A
fromNotFalse = Forall(A, Implies(NotEquals(A, FALSE), A), domain=BOOLEANS)

# forall_{A, B | inBool(B)} [Not(B) => Not(A)] => [A=>B] 
transpositionFromNegated = Forall((A, B), Implies(Implies(Not(B), Not(A)), Implies(A, B)), conditions=inBool(B))

# forall_{A, B | inBool(B)}  [A=>B] => [A => Not(Not(B))]
doubleNegateConclusion = Forall((A, B), Implies(Implies(A, B), Implies(A, Not(Not(B)))), conditions=inBool(B))

# forall_{A, B in BOOLEANS} [Not(B) => A] => [Not(A)=>B] 
transpositionFromNegatedHypothesis = Forall((A, B), Implies(Implies(Not(B), A), Implies(Not(A), B)), domain=BOOLEANS)

# forall_{A, B | inBool(B)} [B => Not(A)] => [A=>Not(B)] 
transpositionFromNegatedConclusion = Forall((A, B), Implies(Implies(B, Not(A)), Implies(A, Not(B))), conditions=inBool(B))

# forall_{A, B in BOOLEANS} [B=>A] => [Not(A) => Not(B)] 
transpositionToNegated = Forall((A, B), Implies(Implies(B, A), Implies(Not(A), Not(B))), domain=BOOLEANS)

# TRUE != FALSE
trueNotFalse = NotEquals(TRUE, FALSE)

# forall_{A} A => (A != FALSE)
notEqualsFalse = Forall(A, Implies(A, NotEquals(A, FALSE)))

# inBool(TRUE)
trueInBool = inBool(TRUE)

# inBool(FALSE)
falseInBool = inBool(FALSE)

# forall_{P} [forall_{A in BOOLEANS} P(A)] => [P(TRUE) and P(FALSE)]
unfoldForallOverBool = Forall(P, Implies(Forall(A, PofA, domain=BOOLEANS), And(PofTrue, PofFalse)))

# forall_{A} A=TRUE => inBool(A)
inBoolIfEqTrue = Forall(A, Implies(Equals(A, TRUE), inBool(A)))

# forall_{A} TRUE=A => inBool(A)
inBoolIfEqTrueRev = Forall(A, Implies(Equals(TRUE, A), inBool(A)))

# forall_{A} A=FALSE => inBool(A)
inBoolIfEqFalse = Forall(A, Implies(Equals(A, FALSE), inBool(A)))

# forall_{A} FALSE=A => inBool(A)
inBoolIfEqFalseRev = Forall(A, Implies(Equals(FALSE, A), inBool(A)))

# forall_{A, B, C in BOOLEANS} (A=>C and B=>C) => ((A or B) => C)
hypotheticalDisjunction = Forall((A, B, C), Implies(And(Implies(A, C), Implies(B, C)), Implies(Or(A, B), C)), domain=BOOLEANS)

# forall_{P} [P(TRUE) and P(FALSE)] => [forall_{A in BOOLEANS} P(A)]
foldForallOverBool = Forall(P, Implies(And(PofTrue, PofFalse), Forall(A, PofA, domain = BOOLEANS)))

# forall_{P} [P(TRUE) and P(FALSE)] => {[forall_{A in BOOLEANS} P(A)] = TRUE}
forallBoolEvalTrue = Forall(P, Implies(And(PofTrue, PofFalse), Equals(Forall(A, PofA, domain=BOOLEANS), TRUE)))

# forall_{P, ..Q.., ..R.., S} [forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)]
#   => forall_{..x.., ..y..  in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
forallBundling = Forall((P, etcQ, etcR, S), Implies(Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc), Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc))))

# forall_{P, ..Q.., ..R.., S} forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) => forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..) 
forallUnraveling = Forall((P, etcQ, etcR, S), Implies(Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))

# forall_{A, B in BOOLEANS} (A <=> B) => (A = B)
iffOverBoolImplEq = Forall((A, B), Implies(Iff(A, B), Equals(A, B)), domain=BOOLEANS)

# forall_{A in booleans} A = Not(Not(A))
doubleNegationEquiv = Forall(A, Equals(A, Not(Not(A))), domain=BOOLEANS)

# forall_{P, ..Q.., ..R.., S} [forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) = forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)]
forallBundledEquiv = Forall((P, etcQ, etcR, S), Equals(Forall((xEtc, yEtc), PxyEtc, S, (etc_QxEtc, etc_RyEtc)), Forall(xEtc, Forall(yEtc, PxyEtc, S, etc_RyEtc), S, etc_QxEtc)))

# forall_{P, ..Q.., S} [forall_{..x.. in S | ..Q(..x..)..} P(..x..)] = [forall_{..x.. in S | ..Q(..x..)..} {P(..x..)=TRUE}]
forallEqTrueEquiv = Forall((P, etcQ, S), Equals(Forall(xEtc, PxEtc, S, etc_QxEtc), Forall(xEtc, Equals(PxEtc, TRUE), S, etc_QxEtc)))

# forall_{A, B in BOOLEANS} (A => B) in BOOLEANS                                                                                                        
implicationClosure = Forall((A, B), inBool(Implies(A, B)), domain=BOOLEANS)

# forall_{A, B in BOOLEANS} (A <=> B) in BOOLEANS                                                                                                        
iffClosure = Forall((A, B), inBool(Iff(A, B)), domain=BOOLEANS)

# forall_{A, B in BOOLEANS} (A and B) in BOOLEANS                                                                                                        
conjunctionClosure = Forall((A, B), inBool(And(A, B)), domain=BOOLEANS)

# forall_{A, B in BOOLEANS} (A or B) in BOOLEANS                                                                                                        
disjunctionClosure = Forall((A, B), inBool(Or(A, B)), domain=BOOLEANS)

# forall_{A in BOOLEANS} Not(A) in BOOLEANS                                                                                                        
negationClosure = Forall(A, inBool(Not(A)), domain=BOOLEANS)

# forall_{A in BOOLEANS} [A => FALSE] => Not(A)                                            
hypotheticalContradiction = Forall(A, Implies(Implies(A, FALSE), Not(A)), domain=BOOLEANS) 

# forall_{P, ..Q.., S} [notexists_{..x.. in S | ..Q(..x..)..} P(..x..) = forall_{..x.. in S | ..Q(..x..)..} (P(..x..) != TRUE)]
existsDefNegation = Forall((P, etcQ, S), Equals(NotExists(xEtc, PxEtc, S, etc_QxEtc), Forall(xEtc, NotEquals(PxEtc, TRUE), S, etc_QxEtc)))

# forall_{P, ..Q.., S} notexists_{..x.. in S | ..Q(..x..)..} P(..x..) => Not(exists_{..x.. in S | ..Q(..x..)..} P(..x..))
notExistsUnfolding = Forall((P, etcQ, S), Implies(NotExists(xEtc, PxEtc, S, etc_QxEtc), Not(Exists(xEtc, PxEtc, S, etc_QxEtc))))

# forall_{P, ..Q.., S} Not(Exists_{..x.. in S | ..Q(..x..)..} P(..x..)) => NotExists_{..x.. in S | ..Q(..x..)..} P(..x..)
notExistsFolding = Forall((P, etcQ, S), Implies(Not(Exists(xEtc, PxEtc, S, etc_QxEtc)), NotExists(xEtc, PxEtc, S, etc_QxEtc)))

# forall_{P, ..Q.., S} [exists_{x in S | ..Q(..x..)..} P(..x..)] in BOOLEANS
existsInBool = Forall((P, etcQ, S), inBool(Exists(xEtc, PxEtc, S, etc_QxEtc)))

# forall_{P, ..Q.., S} forall_{x in S | ..Q(..x..)..} [P(..x..) => exists_{..y.. | ..Q(..y..)..} P(..y..)]
existenceByExample = Forall((P, etcQ, S), Forall(xEtc, Implies(PxEtc, Exists(yEtc, PyEtc, S, etc_QyEtc)), S, etc_QxEtc))

# forall_{P, ..Q.., S} [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))] => [Not(forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
existsNotImpliesNotForall = Forall((P, etcQ, S), Implies(Exists(xEtc, Not(PxEtc), S, etc_QxEtc), Not(Forall(xEtc, PxEtc, S, etc_QxEtc))))

# forall_{P, ..Q.., S} forall_{..x.. in S | ..Q(..x..)..} P(..x..) => NotExists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))
forallImpliesNotExistsNot = Forall((P, etcQ, S), Implies(Forall(xEtc, PxEtc, S, etc_QxEtc), NotExists(xEtc, Not(PxEtc), S, etc_QxEtc)))

# forall_{P} [(P(TRUE) = PofTrueVal) and (P(FALSE) = PofFalseVal)] => {[forall_{A in BOOLEANS} P(A)] = FALSE}, assuming PofTrueVal=FALSE or PofFalseVal=FALSE
def _forallBoolEvalFalse(PofTrueVal, PofFalseVal):
    return Forall(P, Implies(And(Equals(PofTrue, PofTrueVal), Equals(PofFalse, PofFalseVal)), Equals(Forall(A, PofA, domain=BOOLEANS), FALSE)))
forallBoolEvalFalseViaFF = _forallBoolEvalFalse(FALSE, FALSE)
forallBoolEvalFalseViaFT = _forallBoolEvalFalse(FALSE, TRUE)
forallBoolEvalFalseViaTF = _forallBoolEvalFalse(TRUE, FALSE)

booleanTheorems.finish(locals())
