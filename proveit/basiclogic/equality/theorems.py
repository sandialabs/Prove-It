from proveit.statement import Theorems
from proveit.expression import Operation
from eqOps import Equals, NotEquals
from proveit.basiclogic.boolean.boolOps import Implies, Not, And
from proveit.basiclogic.boolean.quantifiers import Forall
from proveit.basiclogic.boolean.boolSet import TRUE, FALSE, inBool
from proveit.basiclogic.variables import A, a, b, c, x, y, z, f, P
from proveit.basiclogic.simpleExpr import fa, fb, fab, fx, fy, fxy, Px, Py

equalityTheorems = Theorems(__package__, locals())

# forall_{P, x, y} {(x=y) => [P(y) => P(x)]}
lhsSubstitution = Forall((P, x, y), Implies(Equals(x, y), Implies(Py, Px)))

# forall_{P, x, y} {(x=y) => [P(x) => P(y)]}
rhsSubstitution = Forall((P, x, y), Implies(Equals(x, y), Implies(Px, Py)))

# forall_{f, x, a, c} (x=a) => {[f(a)=c] => [f(x)=c]}
unaryEvaluation = Forall((f, x, a, c), Implies(Equals(x, a), Implies(Equals(fa, c), Equals(fx, c))))

# forall_{f, x, y, a, b} (x=a and y=b) => [f(x, y) = f(a, b)]
binarySubstitution = Forall((f, x, y, a, b), Implies(And(Equals(x, a), Equals(y, b)), Equals(fxy, fab)))

# forall_{f, x, y, a, b, c} [x=a and y=b] => {[f(a, b)=c] => [f(x, y)=c]}
binaryEvaluation = Forall((f, x, y, a, b, c), Implies(And(Equals(x, a), Equals(y, b)), Implies(Equals(fab, c), Equals(fxy, c))))

# forall_{x, y} [x != y] => Not([x = y])
unfoldNotEquals = Forall((x, y), Implies(NotEquals(x, y), Not(Equals(x, y))))

# forall_{x, y} Not([x = y]) => [x != y]
foldNotEquals = Forall((x, y), Implies(Not(Equals(x, y)), NotEquals(x, y)))

# forall_{x, y} (x != y) => (y != x)
notEqualsSymmetry = Forall((x, y), Implies(NotEquals(x, y), NotEquals(y, x)))

# forall_{x, y} (x != y) in BOOLEANS
notEqualsInBool = Forall((x, y), inBool(NotEquals(x, y)))

# forall_{A} (A=FALSE) => [A => FALSE]
contradictionFromFalseEquivalence = Forall(A, Implies(Equals(A, FALSE), Implies(A, FALSE)))

# forall_{A} (FALSE=A) => [A => FALSE]
contradictionFromFalseEquivalenceReversed = Forall(A, Implies(Equals(FALSE, A), Implies(A, FALSE)))

equalityTheorems.finish(locals())
