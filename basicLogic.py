from proveItCore import *
from genericOperations import *
from boolOps import *
from eqOps import *
from setOps import *
import itertools

prevContext = Context.current

# Variable labels used in axioms and theorems below
a = Variable('a')
b = Variable('b')
c = Variable('c')
A = Variable('A')
B = Variable('B')
C = Variable('C')
f = Variable('f')
P = Variable('P')
x = Variable('x')
y = Variable('y')
X = Variable('X')
S = Variable('S')
fa = Operation(f, [a])
fb = Operation(f, [b])
fab = Operation(f, [a, b])
fx = Operation(f, [x])
fy = Operation(f, [y])
fxy = Operation(f, [x, y])
Px = Operation(P, [x])
Py = Operation(P, [y])
Pa = Operation(P, [a])
Pb = Operation(P, [b])
PofA = Operation(P, [A])
PofB = Operation(P, [B])
PofTrue = Operation(P, [TRUE])
PofFalse = Operation(P, [FALSE])
Q = Variable('Q')
Qx = Operation(Q, [x])
Ax = Operation(A, [x])
Bx = Operation(B, [x])

# Basic set axioms (just to the point of defining what it is to be in the set of booleans)

Context.current = sets

# forall_{x, y} [x in Singleton(y)] = [x = y]
singletonDef = sets.stateAxiom(Forall([x, y], Equals(In(x, Singleton(y)), Equals(x, y))))

# forall_{x, A, B} [x in (A union B)] <=> [(x in A) or (x in B)]
unionDef = sets.stateAxiom(Forall([x, A, B], Iff(In(x, Union(A, B)), Or(In(x, A), In(x, B)))))


# Axioms related to booleans, some simple functions to apply them, and simple related derivations

Context.current = booleans

# BOOLEANS = {TRUE} union {FALSE}
boolsDef = booleans.stateAxiom(Equals(BOOLEANS, Union(Singleton(TRUE), Singleton(FALSE))))

# forall_{x, S} (x in S) in BOOLEANS
inSetIsInBool = booleans.stateAxiom(Forall([x, S], In(In(x, S), BOOLEANS)))

def inBool(X):
    return In(X, BOOLEANS)

"""
# forall_{P, Q} [(forall_{x | Q(x)} P(x)) <=> (forall_{x} Q(x) => P(x))]
forallSuchThatDef = booleans.stateAxiom(Forall([P, Q], Iff(Forall([x], Px, [Qx]), Forall([x], Implies(Qx, Px)))))
"""

# forall_{P} [exists_{x} P(x) <=> Not(forall_{x} Not(P(x)))]
existsDef = booleans.stateAxiom(Forall([P], Iff(Exists([x], Px), Not(Forall([x], Not(Px))))))

# forall_{P, Q} {exists_{x | Q(x)} P(x) <=> exists_{x} [P(x) and Q(x)]}
existsSuchThatDef = booleans.stateAxiom(Forall([P, Q], Iff(Exists([x], Px, [Qx]), Exists([x], And(Px, Qx)))))

# FALSE != TRUE
falseNotTrue = booleans.stateAxiom(NotEquals(FALSE, TRUE))

# {TRUE} union Complement({TRUE}) = EVERYTHING
#trueCompletion = Union(Singleton(TRUE), Complement(Singleton(TRUE))).deriveCompletion()

# TRUE is a true statement
trueAxiom = booleans.stateAxiom(TRUE)
    
# Truth table for NOT
notF = booleans.stateAxiom(Equals(Not(FALSE), TRUE))
notT = booleans.stateAxiom(Equals(Not(TRUE), FALSE))

# Further defining property of NOT needed in addition to the truth table
# because the truth table is ambiguous regarding inputs neither TRUE nor FALSE.

# forall_{A} not(A) => [A=FALSE]
notImpliesEqF = booleans.stateAxiom(Forall([A], Implies(Not(A), Equals(A, FALSE))))


# Truth table for AND
andTT = booleans.stateAxiom(Equals(And(TRUE, TRUE), TRUE))
andTF = booleans.stateAxiom(Equals(And(TRUE, FALSE), FALSE))
andFT = booleans.stateAxiom(Equals(And(FALSE, TRUE), FALSE))
andFF = booleans.stateAxiom(Equals(And(FALSE, FALSE), FALSE))

# Further defining properties of AND needed in addition to the truth table
# because the truth table is ambiguous if we don't know that inputs are TRUE or FALSE.

# forall_{A, B} A and B => A
andImpliesLeft = booleans.stateAxiom(Forall([A, B], Implies(And(A, B), A)))
# forall_{A, B} A and B => B
andImpliesRight = booleans.stateAxiom(Forall([A, B], Implies(And(A, B), B)))


# Truth table for OR
orTT = booleans.stateAxiom(Equals(Or(TRUE, TRUE), TRUE))
orTF = booleans.stateAxiom(Equals(Or(TRUE, FALSE), TRUE))
orFT = booleans.stateAxiom(Equals(Or(FALSE, TRUE), TRUE))
orFF = booleans.stateAxiom(Equals(Or(FALSE, FALSE), FALSE))

# forall_{A, B} (A <=> B) = [(A => B) and (B => A)]
iffDef = booleans.stateAxiom(Forall([A, B], Equals(Iff(A, B), And(Implies(A, B), Implies(B, A)))))

# forall_{A} A => (A = TRUE)
equalsTrueIntro = booleans.stateAxiom(Forall([A], Implies(A, Equals(A, TRUE))))
# forall_{A} (A = TRUE) => A
equalsTrueElim = booleans.stateAxiom(Forall([A], Implies(Equals(A, TRUE), A)))

def deriveStatementEqTrue(statement):
    '''
    For a given statement, derive statement = TRUE given statement.
    '''
    return equalsTrueIntro.specialize({A:statement}).deriveConclusion()

# forall_{A | Not(A=T)} Not(TRUE => A)
falseImplication = booleans.stateAxiom(Forall([A], Not(Implies(TRUE, A)), [NotEquals(A, TRUE)]))

# forall_{A | inBool(A)} [Not(A) => FALSE] => A
hypotheticalContraNegation = booleans.stateAxiom(Forall([A], Implies(Implies(Not(A), FALSE), A), [inBool(A)]))
# Note that implies has a deriveContradiction method that applies this axiom.

# forall_{A} A => TRUE, by a trivial hypothetical reasoning
trueConclusion = Implies(A, TRUE).generalize([A]).qed()

# forall_{A} A => A, by a trivial hypothetical reasoning
selfImplication = Implies(A, A).generalize([A]).qed()

# Not(False)
notF.deriveFromBooleanEquality().qed()

# TRUE and TRUE
andTT.deriveFromBooleanEquality().qed()

# TRUE or TRUE
orTT.deriveFromBooleanEquality().qed()

# TRUE or FALSE
orTF.deriveFromBooleanEquality().qed()

# FALSE or TRUE
orFT.deriveFromBooleanEquality().qed()

# (TRUE => TRUE) = TRUE
impliesTT = deriveStatementEqTrue(trueConclusion.specialize({A:TRUE})).qed()

# (FALSE => TRUE) = TRUE
impliesFT = deriveStatementEqTrue(trueConclusion.specialize({A:FALSE})).qed()

# (FALSE => FALSE) = TRUE
impliesFF = deriveStatementEqTrue(selfImplication.specialize({A:FALSE})).qed()

# (TRUE => FALSE) = FALSE
impliesTF = falseImplication.specialize({A:FALSE}).equateNegatedToFalse().qed()


# Axioms related to equality

Context.current = equality

# forall_{A, B} inBool(A = B)
equalityInBool = equality.stateAxiom(Forall([A, B], inBool(Equals(A, B))))

# forall_{A, B, C} (A=B) => [(B=C) => (A=C)]
equalsTransitivity = equality.stateAxiom(Forall([A, B, C], Implies(Equals(A, B), Implies(Equals(B,C), Equals(A, C)))))
# forall_{A} A=A
equalsReflexivity = equality.stateAxiom(Forall([A], Equals(A, A)))
# forall_{A, B} A=B => B=A
equalsSymmetry = equality.stateAxiom(Forall([A, B], Implies(Equals(A, B), Equals(B, A))))

# forall_{A, B} [A != B] = Not([A = B])
notEqualsDef = equality.stateAxiom(Forall([A, B], Equals(NotEquals(A, B), Not(Equals(A, B)))))

# forall_{f, x, y} [(x=y) => f(x)=f(y)]
substitutionAxiom = equality.stateAxiom(Forall([f, x, y], Implies(Equals(x, y), Equals(fx, fy))))


# Using substitution

def substitution(equivalence, function):
    '''
    Given an equivalence expression of the form x=y and a function f(x),
    return f(x)=f(y) that derives from x=y.
    '''
    assert isinstance(equivalence, Equals)
    assert isinstance(function, Function) or isinstance(function, Variable) or isinstance(function, Literal)
    subMap = SubstitutionMap({x:equivalence.lhs, y:equivalence.rhs, f:function})
    return substitutionAxiom.specialize(subMap).deriveConclusion()

# forall_{f, x, a, c} (x=a) => {[f(a)=c] => [f(x)=c]}
def unaryEvaluationDerivation():
    # x=a, hypothesis
    x_eq_a = Equals(x, a)
    # [f(x) = f(a)] given x=a
    substitution(x_eq_a, Function(fx, [x])).prove({x_eq_a})
    # [f(a)=c] => [f(x)=c] given x=a
    conclusion = equalsTransitivity.specialize({A:fx, B:fa, C:c}).deriveConclusion().prove({x_eq_a})
    # forall_{f, x, a, c} (x=a) => {[f(a)=c] => [f(x)=c]}
    return Implies(x_eq_a, conclusion).generalize([f, x, a, c]).qed()
unaryEvaluation = unaryEvaluationDerivation()  

# forall_{f, x, y, a, b} (x=a and y=b) => [f(x, y) = f(a, b)]
def binarySubstitutionDerivation():
    # hypothesis = (x=a and y=b)
    hypothesis = And(Equals(x, a), Equals(y, b))
    # f(x, y) = f(a, y) given hypothesis
    fxy_eq_fay = substitution(hypothesis.deriveLeft(), Function(fxy, [x])).prove({hypothesis})
    # f(a, y) = f(a, b) given hypothesis
    substitution(hypothesis.deriveRight(), Function(fab, [b])).prove({hypothesis})
    # f(x, y) = f(a, b) given hypothesis
    conclusion = equalsTransitivity.specialize({A:fxy, B:fxy_eq_fay.rhs, C:fab}).deriveConclusion().deriveConclusion().prove({hypothesis})
    # forall_{f, x, y, a, b} (x=a and y=b) => [f(x, y) = f(a, b)]
    return Implies(hypothesis, conclusion).generalize([f, x, y, a, b]).qed()
binarySubstitution = binarySubstitutionDerivation()  

# forall_{f, x, y, a, b, c} [x=a and y=b] => {[f(a, b)=c] => [f(x, y)=c]}
def binaryEvaluationDerivation():
    # hypothesis = (x=a and y=b)
    hypothesis = And(Equals(x, a), Equals(y, b))
    # [f(x, y) = f(a, b)] given hypothesis
    binarySubstitution.specialize().deriveConclusion().prove({hypothesis})
    # [f(a, b)=c] => [f(x, y)=c] given hypothesis
    conclusion = equalsTransitivity.specialize({A:fxy, B:fab, C:c}).deriveConclusion().prove({hypothesis})
    # forall_{f, x, y, a, b, c} [x=a and y=b] => {[f(a, b)=c] => [f(x, y)=c]}
    return Implies(hypothesis, conclusion).generalize([f, x, y, a, b, c]).qed()
binaryEvaluation = binaryEvaluationDerivation()  

Context.current = booleans

# forall_{P, x, y} {(x=y) => [P(x) => P(y)]}
def statementSubstitutionDerivation():
    # P(x) = TRUE given P(x)
    Px_eq_T = deriveStatementEqTrue(Px).prove({Px})
    # (x = y) => [P(x) = P(y)]
    substitutionAxiom.specialize({f:P}).prove()
    # [P(x) = P(y)] => [P(y) = P(x)]
    equalsSymmetry.specialize({A:Px, B:Py}).prove()
    # P(y), given P(y)=P(x) and P(x)=TRUE
    equalsTransitivity.specialize({A:Py, B:Px, C:TRUE}).deriveConclusion().deriveConclusion().deriveFromBooleanEquality().prove({Px_eq_T, Equals(Px, Py)})
    # forall_{P, x, y} {(x = y) => [P(x) => P(y)]}, by (nested) hypothetical reasoning
    return Implies(Equals(x, y), Implies(Px, Py)).generalize([P, x, y]).qed()
statementSubstitutionThm = statementSubstitutionDerivation()

def statementSubstitution(equivalence, function):
    '''
    Given an equivalence expression of the form x=y and a function P(x),
    return P(x) => P(y) that derives from x=y.
    '''
    assert isinstance(function, Function) or isinstance(function, Variable) or isinstance(function, Literal)
    subMap = {x:equivalence.lhs, y:equivalence.rhs, P:function}
    return statementSubstitutionThm.specialize(subMap).deriveConclusion()

def substitute(equivalence, function):
    '''
    Given an equivalence expression of the form x=y and a function P(x),
    return P(y) that derives from x=y and P(x).
    '''
    return statementSubstitution(equivalence, function).deriveConclusion()

def deriveViaEquivalence(equivalence):
    '''
    Given an equivalence expression of the form A=B, derive
    B from A.
    '''
    return substitute(equivalence, Function(X, [X]))


# Some rudimentary theorems for implications

Context.current = booleans

# forall_{A, B} (A <=> B) => (A => B)
iffImpliesRight = Implies(Iff(A, B), iffDef.specialize().deriveViaEquivalence().deriveLeft()).generalize([A, B]).qed()

# forall_{A, B} (A <=> B) => (B => A)
iffImpliesLeft = Implies(Iff(A, B), iffDef.specialize().deriveViaEquivalence().deriveRight()).generalize([A, B]).qed()

# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
def unfoldInBoolDerivation():
    # [A in {TRUE} union {FALSE}] given inBool(A)
    substitute(boolsDef, Function(In(A, X), [X])).prove({inBool(A)})
    # (A in {TRUE}) or (A in {FALSE}) given inBool(A)
    unionDef.specialize({x:A, A:Singleton(TRUE), B:Singleton(FALSE)}).deriveRight().prove({inBool(A)})
    # A=TRUE or (A in {FALSE} given inBool(A)
    substitute(singletonDef.specialize({x:A, y:TRUE}), Function(Or(X, In(A, Singleton(FALSE))), [X])).prove({inBool(A)})
    # A=TRUE or A=FALSE given inBool(A)
    conclusion = substitute(singletonDef.specialize({x:A, y:FALSE}), Function(Or(Equals(A, TRUE), X), [X])).prove({inBool(A)})
    # forall_{A} inBool(A) => (A=TRUE or A=FALSE)
    return Implies(inBool(A), conclusion).generalize([A]).qed()
unfoldInBool = unfoldInBoolDerivation()    

# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
def foldInBoolDerivation():
    # hypothesis = (A=TRUE or A=FALSE)
    hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
    # (A=TRUE) or (A in {FALSE}) given hypothesis
    substitute(singletonDef.specialize({x:A, y:FALSE}).deriveReversed(), Function(Or(Equals(A, TRUE), X), [X])).prove({hypothesis})
    # (A in {TRUE}) or (A in {FALSE}) given hypothesis
    substitute(singletonDef.specialize({x:A, y:TRUE}).deriveReversed(), Function(Or(X, In(A, Singleton(FALSE))), [X])).prove({hypothesis})
    # [A in {TRUE} union {FALSE}] given hypothesis
    unionDef.specialize({x:A, A:Singleton(TRUE), B:Singleton(FALSE)}).deriveLeft().prove({hypothesis})
    # inBool(A) given hypothesis
    substitute(boolsDef.deriveReversed(), Function(In(A, X), [X])).prove({hypothesis})
    # forall_{A} (A=TRUE or A=FALSE) => inBool(A)
    return Implies(hypothesis, inBool(A)).generalize([A]).qed()
foldInBool = foldInBoolDerivation()    

# TRUE = TRUE
trueEqTrue = equalsReflexivity.specialize({A:TRUE}).qed()
# FALSE = FALSE
falseEqFalse = equalsReflexivity.specialize({A:FALSE}).qed()

# forall_{A, B} [A != B] => Not([A = B])
unfoldNotEquals = notEqualsDef.specialize().implicationViaEquivalence().generalize([A, B]).qed()

# forall_{A, B} Not([A = B]) => [A != B]
foldNotEquals = notEqualsDef.specialize().deriveReversed().implicationViaEquivalence().generalize([A, B]).qed()

# forall_{A, B} A => (B => (A and B))
def conjunctionIntroDerivation():
    # TRUE=A given A
    TeqA = deriveStatementEqTrue(A).deriveReversed().prove({A})
    # TRUE=B given B
    TeqB = deriveStatementEqTrue(B).deriveReversed().prove({B})
    # (TRUE and B) given B via (TRUE and TRUE)
    substitute(TeqB, Function(And(TRUE, X), [X])).prove({B})
    # B => (TRUE and B), by hypothetical reasoning
    Implies(B, And(TRUE, B)).prove()
    # [B => A and B] given A, because [B => TRUE and B]
    substitute(TeqA, Function(Implies(B, And(X, B)), [X])).prove({A})
    # A => (B => (A and B)), by nested hypothetical reasoning
    return Implies(A, Implies(B, And(A, B))).generalize([A, B]).qed()
conjunctionIntro = conjunctionIntroDerivation()

def compose(exprA, exprB):
    '''
    Returns [exprA and exprB] derived from each separately.
    '''
    return conjunctionIntro.specialize({A:exprA, B:exprB}).deriveConclusion().deriveConclusion()

# (TRUE <=> TRUE) = TRUE
def iffTTderivation():
    # (TRUE <=> TRUE) = (TRUE => TRUE) and (TRUE => TRUE)
    iffSpecTT = iffDef.specialize({A:TRUE, B:TRUE}).prove()
    # [(TRUE => TRUE) and (TRUE => TRUE)] = TRUE, via (TRUE and TRUE) = TRUE
    rhsEqT = substitution(impliesTT, Function(And(X, X), [X])).applyTransitivity(andTT).prove()
    # (TRUE <=> TRUE) = TRUE
    return iffSpecTT.applyTransitivity(rhsEqT).qed()
iffTT = iffTTderivation()

# (FALSE <=> FALSE) = TRUE
def iffFFderivation():
    # (FALSE <=> FALSE) = (FALSE => FALSE) and (FALSE => FALSE)
    iffSpecFF = iffDef.specialize({A:FALSE, B:FALSE}).prove()
    # [(FALSE => FALSE) and (FALSE => FALSE)] = TRUE, via (TRUE and TRUE) = TRUE
    rhsEqT = substitution(impliesFF, Function(And(X, X), [X])).applyTransitivity(andTT).prove()
    # (FALSE <=> FALSE) = TRUE
    return iffSpecFF.applyTransitivity(rhsEqT).qed()
iffFF = iffFFderivation()

# (TRUE <=> FALSE) = FALSE
def iffTFderivation():
    # (TRUE <=> FALSE) = (TRUE => FALSE) and (FALSE => TRUE)
    iffSpecTF = iffDef.specialize({A:TRUE, B:FALSE}).prove()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = [FALSE and (FALSE => TRUE)]
    rhsEqFandFimplT = substitution(impliesTF, Function(And(X, impliesFT.lhs), [X])).prove()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = [FALSE and TRUE]
    rhsEqFandT = rhsEqFandFimplT.applyTransitivity(substitution(impliesFT, Function(And(FALSE, X), [X]))).prove()
    # [(TRUE => FALSE) and (FALSE => TRUE)] = FALSE
    rhsEqF = rhsEqFandT.applyTransitivity(andFT).prove()
    # (TRUE <=> FALSE) = FALSE
    return iffSpecTF.applyTransitivity(rhsEqF).qed()
iffTF = iffTFderivation()

# (FALSE <=> TRUE) = FALSE
def iffFTderivation():
    # (FALSE <=> TRUE) = (FALSE => TRUE) and (TRUE => FALSE)
    iffSpecFT = iffDef.specialize({A:FALSE, B:TRUE}).prove()
    # [(FALSE => TRUE) and (TRUE => FALSE)] = [(FALSE => TRUE) and FALSE]
    rhsEqFimplTandF = substitution(impliesTF, Function(And(impliesFT.lhs, X), [X])).prove()
    # [(FALSE => TRUE) and (TRUE => FALSE)] = [TRUE and FALSE]
    rhsEqTandF = rhsEqFimplTandF.applyTransitivity(substitution(impliesFT, Function(And(X, FALSE), [X]))).prove()
    # [(FALSE => TRUE) and (TRUE => FALSE)] = FALSE
    rhsEqF = rhsEqTandF.applyTransitivity(andTF).prove()
    # (TRUE <=> FALSE) = FALSE
    return iffSpecFT.applyTransitivity(rhsEqF).qed()
iffFT = iffFTderivation()

# forall_{A} Not(A) => [A => FALSE]
def contradictionFromNegationDerivation():
    # FALSE given Not(A) and A
    deriveViaEquivalence(Not(A).equateNegatedToFalse()).prove({Not(A), A})
    return Implies(Not(A), Implies(A, FALSE)).generalize([A]).qed()
contradictionFromNegation = contradictionFromNegationDerivation()

# forall_{A} (A=FALSE) => Not(A)
def notFromEqFalseDerivation():
    # AeqF := (A=F)
    AeqF = Equals(A, FALSE)
    # Not(A) given A=FALSE because Not(FALSE)
    notA = substitute(AeqF.deriveReversed(), Function(Not(X), [X])).prove({AeqF})
    return Implies(AeqF, notA).generalize([A]).qed()
notFromEqFalse = notFromEqFalseDerivation()

# forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
def notOrFromNeitherDerivation():
    # Not(A or B) = Not(F or B) given Not(A)
    notAorB_eq_notForB = substitution(Not(A).equateNegatedToFalse(), Function(Not(Or(X, B)), [X])).prove({Not(A)})
    # Not(A or B) = Not(F or F) given Not(A), Not(B)
    notAorB_eq_notForF = notAorB_eq_notForB.applyTransitivity(substitution(Not(B).equateNegatedToFalse(), Function(Not(Or(FALSE, X)), [X]))).prove({Not(A), Not(B)})
    #  Not(A or B) = Not(F) given Not(A), Not(B)
    notAorB_eq_notF = notAorB_eq_notForF.applyTransitivity(substitution(orFF, Function(Not(X), [X]))).prove({Not(A), Not(B)})
    # Not(A or B) given Not(A), Not(B)
    notAorB = notAorB_eq_notF.deriveReversed().deriveViaEquivalence().prove({Not(A), Not(B)})
    # forall_{A, B} Not(A) => [Not(B) => Not(A or B)]
    return Implies(Not(A), Implies(Not(B), notAorB)).generalize([A, B]).qed()
notOrFromNeither = notOrFromNeitherDerivation()

# (A or B) => FALSE given Not(A), Not(B)
notOrFromNeither.specialize().deriveConclusion().deriveConclusion().deriveContradiction().deriveConclusion()

# forall_{A, B | isBool(A)} (A or B) => [Not(B) => A]
def orImpliesLeftIfNotRightDerivation():
    # By contradiction: A given isBool(A), A or B, Not(B)
    assumptions = {inBool(A), Or(A, B), Not(B)}
    Implies(Not(A), FALSE).deriveHypotheticalContradiction().prove(assumptions)
    # forall_{A, B | isBool(A)} (A or B) => [Not(B) => A]
    return Implies(Or(A, B), Implies(Not(B), A)).generalize([A, B], [inBool(A)]).qed()
orImpliesLeftIfNotRight = orImpliesLeftIfNotRightDerivation()

# forall_{A, B | isBool(B)} (A or B) => [Not(A) => B]
def orImpliesRightIfNotLeftDerivation():
    # By contradiction: B given isBool(B), (A or B), Not(A)
    assumptions = {inBool(B), Or(A, B), Not(A)}
    Implies(Not(B), FALSE).deriveHypotheticalContradiction().prove(assumptions)
    # forall_{A, B | isBool(B)} (A or B) => [Not(A) => B]
    return Implies(Or(A, B), Implies(Not(A), B)).generalize([A, B], [inBool(B)]).qed()
orImpliesRightIfNotLeft = orImpliesRightIfNotLeftDerivation()

# forall_{A} A => Not(Not(A))
def doubleNegationDerivation():
    # A=TRUE given A
    AeqT = deriveStatementEqTrue(A)
    # [Not(A)=FALSE] given A=TRUE
    substitution(AeqT, Function(Not(X), [X])).applyTransitivity(notT).prove({AeqT})
    # [Not(A)=FALSE] => Not(Not(A))
    notFromEqFalse.specialize({A:Not(A)}).prove()
    # forall_{A} A => Not(Not(A))
    return Implies(A, Not(Not(A))).generalize([A]).qed()
doubleNegation = doubleNegationDerivation()

def deriveDoubleNegated(statement):
    '''
    Returns Not(Not(statement)) derived from statement
    '''
    return doubleNegation.specialize({A:statement}).deriveConclusion()

# forall_{A | isBool(A)} Not(Not(A)) => A
def fromDoubleNegationDerivation():
    # hypothesis = Not(Not(A))
    hypothesis = booleans.state(Not(Not(A)))
    # FALSE given Not(A), Not(Not(A))
    deriveViaEquivalence(hypothesis.equateNegatedToFalse()).prove({Not(A), hypothesis})
    # [Not(A) => FALSE] => A given isBool(A)
    hypotheticalContraNegation.specialize().prove({inBool(A)})
    # isBool(A) => [Not(Not(A)) => A] via hypothetical reasoning
    return Implies(hypothesis, A).generalize([A], [inBool(A)]).qed()
fromDoubleNegation = fromDoubleNegationDerivation()

# forall_{A | isBool(A)} (A != FALSE) => A
def fromNotEqualFalseDerivation():
    # AnotF = (A != FALSE)
    AnotF = NotEquals(A, FALSE)
    # notAeqF = Not(A = FALSE)
    notAeqF = AnotF.unravel()
    # (A=TRUE or A=FALSE) given inBool(A)
    AeqT_or_AeqF = unfoldInBool.specialize().deriveConclusion().prove({inBool(A)})
    AeqT, AeqF = AeqT_or_AeqF.operands
    # Not(A=FALSE) and (A=TRUE or A=FALSE) given each
    compose(notAeqF, AeqT_or_AeqF).prove({notAeqF, AeqT_or_AeqF})
    # inBool(A=TRUE)
    equalityInBool.specialize({A:A, B:TRUE}).prove()
    # A given isBool(A), Not(A=FALSE)
    orImpliesLeftIfNotRight.specialize({A:AeqT, B:AeqF}).deriveConclusion().deriveConclusion().deriveFromBooleanEquality().prove({inBool(A), notAeqF})
    # forall_{A | isBool(A)} Not(A=FALSE) => A
    return Implies(AnotF, A).generalize([A], [inBool(A)]).qed()
fromNotEqualFalse = fromNotEqualFalseDerivation()

# Not(TRUE) => FALSE
notTimpliesF = notT.implicationViaEquivalence().qed()

# forall_{A, B | isBool(B)} [Not(B) => Not(A)] => [A=>B] 
def transpositionFromNegatedDerivation():
    notBimplNotA = booleans.state(Implies(Not(B), Not(A)))
    # Contradiction proof of B given (Not(B)=>Not(A)) and A and isBool(B):
    # B given isBool(B), (Not(B)=>Not(A)), A
    Implies(Not(B), FALSE).deriveHypotheticalContradiction().prove({inBool(B), notBimplNotA, A})
    # A=FALSE given Not(B)=>Not(A) and Not(B)
    AeqF = notBimplNotA.deriveConclusion().equateNegatedToFalse().prove({notBimplNotA, Not(B)})
    # FALSE given A=FALSE and A
    deriveViaEquivalence(AeqF).prove({Equals(A, FALSE), A})
    # [Not(B) => Not(A)] => [A => B] by nested hypothetical reasoning assuming isBool(B)
    transpositionExpr = Implies(notBimplNotA, Implies(A, B)).prove({inBool(B)})
    # forall_{A, B | isBool(B)} [A => B] => [Not(B) => Not(A)]
    return transpositionExpr.generalize([A, B], [inBool(B)]).qed()
transpositionFromNegated = transpositionFromNegatedDerivation()

# forall_{A, B | isBool(B)}  [A=>B] => [A => Not(Not(B))]
def doubleNegateConclusionDerivation():
    # Not(Not(B)) given B and isBool(B)
    notNotB = deriveDoubleNegated(B).prove({B, inBool(B)})
    # [A=>B] => [A => Not(Not(B))] given isBool(B)
    innerExpr = Implies(Implies(A, B), Implies(A, notNotB)).prove({inBool(B)})
    # forall_{A, B | isBool(B)}  [A=>B] => [A => Not(Not(B))]
    return innerExpr.generalize([A, B], [inBool(B)]).qed()
doubleNegateConclusion = doubleNegateConclusionDerivation()

# forall_{A, B | isBool(A), isBool(B)} [Not(B) => A] => [Not(A)=>B] 
def transpositionFromNegatedHypothesisDerivation():
    # [Not(B) => Not(Not(A))] => [Not(A) => B)]  given isBool(B)
    toConclusion = transpositionFromNegated.specialize({A:Not(A), B:B}).prove({inBool(B)})
    # [Not(B) => A] => [Not(B) => Not(Not(A))] given isBool(A)    
    fromHyp = doubleNegateConclusion.specialize({A:Not(B), B:A}).prove({inBool(A)})
    # [Not(B) => A] => [Not(A)=>B] given isBool(A) and isBool(B)
    transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
    # forall_{A, B | isBool(A), isBool(B)} [Not(B) => A] => [Not(A)=>B] 
    return transpositionExpr.generalize([A, B], [inBool(A), inBool(B)]).qed()
transpositionFromNegatedHypothesis = transpositionFromNegatedHypothesisDerivation()

# forall_{A, B | isBool(B)} [B => Not(A)] => [A=>Not(B)] 
def transpositionFromNegatedConclusionDerivation():
    # isBool(B=FALSE)
    equalityInBool.specialize({A:B, B:FALSE}).prove()
    # [Not(B=FALSE) => Not(A)] => [A => (B=FALSE)], using isBool(B=FALSE)
    midPointBackHalf = transpositionFromNegated.specialize({A:A, B:Equals(B, FALSE)}).prove()
    # [(B != FALSE) => Not(A)] => [Not(B=FALSE) => Not(A)]
    midPointFrontHalf = statementSubstitution(notEqualsDef.specialize({A:B, B:FALSE}), Function(Implies(X, Not(A)), [X])).prove()
    # [(B != FALSE) => Not(A)] => [A => (B=FALSE)]
    midPoint = midPointFrontHalf.applySyllogism(midPointBackHalf).prove()
    # B given B != FALSE) and isBool(B)
    notBeqF = NotEquals(B, FALSE)
    notBeqF.deriveFromDoubleNegation().prove({notBeqF, inBool(B)})
    # [B => Not(A)] => [(B != FALSE) => Not(A)] given isBool(B)
    fromHyp = Implies(Implies(B, Not(A)), Implies(notBeqF, Not(A))).prove({inBool(B)})
    # Not(B) given B=FALSE
    BeqF = Equals(B, FALSE)
    BeqF.deriveFromBooleanEquality().prove({BeqF})
    # [A => (B=FALSE)] => [A => Not(B)] given isBool(B)
    toConclusion = Implies(Implies(A, BeqF), Implies(A, Not(B))).prove({inBool(B)})
    # [B => Not(A)] => [A=>Not(B)] given isBool(B)
    transpositionExpr = fromHyp.applySyllogism(midPoint).applySyllogism(toConclusion).prove({inBool(B)})
    # forall_{A, B | isBool(B)} [B => Not(A)] => [A=>Not(B)] 
    return transpositionExpr.generalize([A, B], [inBool(B)]).qed()
transpositionFromNegatedConclusion = transpositionFromNegatedConclusionDerivation()
    
# forall_{A, B | isBool(A), isBool(B)} [B=>A] => [Not(A) => Not(B)] 
def transpositionToNegatedDerivation():
    # [B => Not(Not(A))] => [Not(A)=>Not(B)] given isBool(A), isBool(B)
    toConclusion = transpositionFromNegatedConclusion.specialize({A:Not(A), B:B}).prove({inBool(A), inBool(B)})
    # [B => A] => [B => Not(Not(A))] given isBool(A)
    fromHyp = doubleNegateConclusion.specialize({A:B, B:A}).prove({inBool(A)})
    # [B => A] => [Not(A)=>Not(B)] given isBool(A), isBool(B)
    transpositionExpr = fromHyp.applySyllogism(toConclusion).prove({inBool(A), inBool(B)})
    # forall_{A, B | isBool(A), isBool(B)} [B=>A] => [Not(A) => Not(B)] 
    return transpositionExpr.generalize([A, B], [inBool(A), inBool(B)]).qed()
transpositionToNegated = transpositionToNegatedDerivation()

# forall_{A, B} (A != B) => (B != A)
def notEqualsSymmetryDerivation():
    # isBool(A=B)
    equalityInBool.specialize().prove()
    # isBool(B=A)
    equalityInBool.specialize({A:B, B:A}).prove()
    # Not(A=B) => Not(B=A)
    equalsSymmetry.specialize({A:B, B:A}).applyTransposition().prove()
    # Not(A=B) given (A != B)
    NotEquals(A, B).unravel().prove({NotEquals(A, B)})
    # (B != A) given Not(B=A)
    Not(Equals(B, A)).deriveNotEquals().prove({Not(Equals(B, A))})
    # forall_{A, B} (A != B) => (B != A)
    return Implies(NotEquals(A, B), NotEquals(B, A)).generalize([A, B]).qed()
notEqualsSymmetry = notEqualsSymmetryDerivation()

# TRUE != FALSE
trueNotFalse = falseNotTrue.deriveReversed().qed()

# isBool(TRUE)
def trueIsBoolDerivation():
    # [TRUE or FALSE] 
    orTF.deriveFromBooleanEquality().prove()
    # [TRUE or TRUE=FALSE] via [TRUE or FALSE] and Not(TRUE=FALSE)
    substitute(trueNotFalse.unravel().equateNegatedToFalse().deriveReversed(), Function(Or(TRUE, X), [X])).prove()
    # [TRUE=TRUE or TRUE=FALSE] via [TRUE or TRUE=FALSE] and TRUE=TRUE
    substitute(deriveStatementEqTrue(trueEqTrue).deriveReversed(), Function(Or(X, Equals(TRUE, FALSE)), [X])).prove()
    # isBool(TRUE) via [TRUE=TRUE or TRUE=FALSE]
    foldInBool.specialize({A:TRUE}).prove()
    return inBool(TRUE).qed()
trueIsBool = trueIsBoolDerivation()

# isBool(FALSE)
def falseIsBoolDerivation():
    # [FALSE or TRUE] 
    orFT.deriveFromBooleanEquality().prove()
    # [FALSE or FALSE=FALSE] via [FALSE or TRUE] and FALSE=FALSE
    substitute(deriveStatementEqTrue(falseEqFalse).deriveReversed(), Function(Or(FALSE, X), [X])).prove()
    # [FALSE=TRUE or FALSE=FALSE] via [FALSE or FALSE=FALSE] and Not(FALSE=TRUE)
    substitute(falseNotTrue.unravel().equateNegatedToFalse().deriveReversed(), Function(Or(X, Equals(FALSE, FALSE)), [X])).prove()
    # isBool(FALSE) via [FALSE=TRUE or FALSE=FALSE]
    foldInBool.specialize({A:FALSE}).qed()
    return inBool(FALSE).qed()
falseIsBool = falseIsBoolDerivation()

# forall_{A, B, C | isBool(A), isBool(B), isBool(C)} (A=>C and B=>C) => ((A or B) => C)
def hypotheticalDisjunctionDerivation():
    AorB = Or(A, B)
    AimplC_and_BimplC = And(Implies(A, C), Implies(B, C))
    ABCareBoolInOrder = [inBool(A), inBool(B), inBool(C)]
    ABCareBool = set(ABCareBoolInOrder)
    # Contradiction proof of C given (A=>C and B=>C), (A or B), isBool(A), and isBool(B):
    # C, given Not(C)=>FALSE which will be proven by hypothetical reasoning assuming isBool(A), isBool(B), isBool(C), (A=>C and B=>C) and (A or B)
    Implies(Not(C), FALSE).deriveHypotheticalContradiction()
    # A=>C, B=>C given (A=>C and B=>C)
    AimplC, BimplC = AimplC_and_BimplC.decompose()
    for impl in (AimplC, BimplC): impl.prove({AimplC_and_BimplC})
    # Not(A) given isBool(A), isBool(B), (A=>C and B=>C), Not(C)
    AimplC.applyTransposition().deriveConclusion().prove({inBool(A), inBool(C), AimplC_and_BimplC, Not(C)})
    # B given inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    orImpliesRightIfNotLeft.specialize().deriveConclusion().deriveConclusion().prove(ABCareBool | {AimplC_and_BimplC, AorB, Not(C)})
    # Not(TRUE) given inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    substitute(deriveStatementEqTrue(C), Function(Not(X), [X])).prove(ABCareBool | {AimplC_and_BimplC, AorB, Not(C)})
    # FALSE given inBool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
    deriveViaEquivalence(notT).prove(ABCareBool | {AimplC_and_BimplC, AorB, Not(C)})
    # prove C given isBool(A, B, C), (A=>C and B=>C), (A or B)
    C.prove(ABCareBool | {AimplC_and_BimplC, AorB})
    return Implies(AimplC_and_BimplC, Implies(AorB, C)).generalize([A, B, C], ABCareBoolInOrder).qed()
hypotheticalDisjunction = hypotheticalDisjunctionDerivation()    

# forall_{A, B | inBool(A), inBool(B)} (A <=> B) => (A = B)
def iffImplEqDerivation():
    pass
iffImplEq = iffImplEqDerivation()


# forall_{A, B, C | isBool(A), isBool(B), isBool(C)} (A=>C and B=>C) = ((A or B) => C)


# forall_{A | isBool(A)} P(A) = P(TRUE) and P(FALSE)


# forall_{A | isBool(A)} isBool(Not(A))
def negatedBoolIsBoolDerivation():
    AeqT = booleans.state(Equals(A, TRUE))
    AeqF = booleans.state(Equals(A, FALSE))
    # inBool(A=TRUE)
    equalityInBool.specialize({A:A, B:TRUE}).prove()
    # inBool(A=FALSE)
    equalityInBool.specialize({A:A, B:FALSE}).prove()
    # inBool(inBool(Not(A))
    inSetIsInBool.specialize({x:Not(A), S:BOOLEANS}).prove()
    # {[A=TRUE => isBool(Not(A))] and [A=FALSE => isBool(Not(A))]} => [(A=TRUE or A=FALSE) => isBool(Not(A))]
    conclusion = inBool(Not(A))
    hypoDisjExpr = hypotheticalDisjunction.specialize({A:AeqT, B:AeqF, C:conclusion}).prove()
    # Not(A)=FALSE given A=TRUE via Not(TRUE)=FALSE
    notA_eq_F = substitute(AeqT.deriveReversed(), Function(Equals(Not(X), FALSE), [X])).prove({AeqT, inBool(A)})
    # isBool(Not(A)) given A=TRUE via isBool(FALSE)
    substitute(notA_eq_F.deriveReversed(), Function(inBool(X), [X])).prove({AeqT, inBool(A)})
    # Not(A)=TRUE given A=FALSE via Not(FALSE)=TRUE
    notA_eq_T = substitute(AeqF.deriveReversed(), Function(Equals(Not(X), TRUE), [X])).prove({AeqF, inBool(A)})
    # isBool(Not(A)) given A=FALSE via isBool(TRUE)
    substitute(notA_eq_T.deriveReversed(), Function(inBool(X), [X])).prove({AeqF, inBool(A)})
    # A=TRUE => isBool(Not(A))
    AeqT_implies_conclusion = Implies(AeqT, inBool(Not(A))).prove({inBool(A)})
    # A=FALSE => isBool(Not(A)), derived below as well    
    AeqF_implies_conclusion = Implies(AeqF, inBool(Not(A))).prove({inBool(A)})
    # {[A=TRUE => isBool(Not(A))] and [A=FALSE => isBool(Not(A))]} from each individually
    compose(AeqT_implies_conclusion, AeqF_implies_conclusion).prove({inBool(A)})
    # isBool(A) => (A=TRUE or A=FALSE)
    unfoldInBool.specialize()
    # forall_{A | isBool(A)} isBool(Not(A))
    return hypoDisjExpr.deriveConclusion().deriveConclusion().generalize([A], [inBool(A)]).qed()
negatedBoolIsBool = negatedBoolIsBoolDerivation()

# forall_{A | isBool(A)} [A => FALSE] => Not(A)
def hypotheticalContradictionDerivation():
    # isBool(Not(A)) given isBool(A)
    negatedBoolIsBool.specialize().prove({inBool(A)})
    # [Not(Not(A)) => FALSE] => Not(A) given isBool(A)
    hypotheticalContraNegation.specialize({A:Not(A)}).prove({inBool(A)})
    # A given Not(Not(A)) and inBool(A)
    Not(Not(A)).deriveFromDoubleNegation().prove({inBool(A), Not(Not(A))})
    # forall_{A | isBool(A)} [A => FALSE] => Not(A)
    return Implies(Implies(A, FALSE), Not(A)).generalize([A], [inBool(A)]).qed()
hypotheticalContradiction = hypotheticalContradictionDerivation()


def evaluateBooleanBinaryOperation(operation, baseEvalFn):
    prevContext = Context.current
    Context.current = booleans
    _x = operation.operands[0]
    _y = operation.operands[1]
    operator = operation.operator
    if (_x == TRUE or _x == FALSE) and (_y == TRUE or _y == FALSE):
        evaluation = baseEvalFn(_x, _y)
    elif (_x == TRUE or _x == FALSE):
        _b = _y.evaluate().rhs
        _c = baseEvalFn(_x, _b).rhs
        dummyVar = _x.safeDummyVar() # var that isn't in _x
        _f = Function(Operation(operator, [_x, dummyVar]), [dummyVar])
        evaluation = unaryEvaluation.specialize({f:_f, x:_y, a:_b, c:_c}).deriveConclusion().deriveConclusion()
    elif (_y == TRUE or _y == FALSE):
        _a = _x.evaluate().rhs, 
        _c = baseEvalFn(_a, _y).rhs
        dummyVar = _y.safeDummyVar() # var that isn't in _y
        _f = Function(Operation(operator, [dummyVar, _y]), [dummyVar])
        evaluation = unaryEvaluation.specialize({f:_f, x:_x, a:_a, c:_c}).deriveConclusion().deriveConclusion()
    else:
        xEval = _x.evaluate()
        yEval = _y.evaluate()
        compose(xEval, yEval)
        _a, _b = xEval.rhs, yEval.rhs, 
        _c = baseEvalFn(_a, _b).rhs
        _f = Function(Operation(operator, [a, b]), [a, b])
        # f(_x, _y) = _c
        evaluation = binaryEvaluation.specialize({f:_f, x:_x, y:_y, a:_a, b:_b, c:_c}).deriveConclusion().deriveConclusion()
    Context.current = prevContext
    return evaluation



"""
# forall_{A,B|isBool(A),isBool(B)} A<=>B => [A=B]

# forall_{Q} Q(a) => exists_{x} Q(x)
def existenceByExampleDerivation():
    # Not[forall_{x} Not(Q(x))] => exists_{x} Q(x)
    existsDef.specialize({P:Q}).deriveLeft()
    # forall_x_NotQx = forall_{x} Not(Q(x))
    forall_x_NotQx = booleans.state(Forall([x], Not(Qx)))
    # We'll derive Not[forall_{x} Not(Q(x))] by contradiction 
    # from Not(Not[forall_{x} Not(Q(x))]=TRUE) => FALSE
    deriveByContradiction(Not(forall_x_NotQx))   
    # forall_{x} Not(Q(x)) => Not(Q(a))
    forall_x_NotQx.specialize({x:a})
    # FALSE given forall_{x} Not(Q(x)) and Q(a)
    deriveViaEquivalence(substitute(deriveStatementEqTrue(Qx), Function(Not(X), [X])))
    
    

existenceByExample = None#existenceByExampleDerivation()


# forall_{y, Q} [exists_{x | Q(x)} x=y <=> Q(y)
def existsEquivIffConditionMetDerivation():
    # exists_{x | Q(x)} x=y <=> Not(forall_{x | Q(x)} Not(x=y))]
    existsSuchThatDef.specialize({P:Function(Equals(x, y), [x])})
    # Q(y) => Not(y=y) => False
    # forall_{x|Q(x)} Not(x=y) => [Q(y) => Not(y=y)]
    
    Forall([x], NotEquals(x, y), [Qx])
    
    # Not(P(y)) => Not(forall_{x} P(x))

    
    
    # [Q(x) => Not(x=y)] => [Not((x=y)=T) => Not(Q(x)=T)]
    transposition.specialize({A:Qx, B:NotEquals(x, y)})
    
    # x=y => Not(Q(x))
    # x=y => [Q(x)=>Q(y)] 
    statementSubstitution.specialize({P:Function(Qx, [x])})
    
    substitutionAxiom
    # x=y => [Q(y)=>Q(x)] 
    # Q(x) => Not(x=y) 
    
    
    
existsEquivIffConditionMet = None #existsEquivIffConditionMetDerivation()
"""
registerTheorems(__name__, locals())

Context.current = defaultContext
