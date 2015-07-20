from proveit.statement import Axioms
from proveit.expression import Operation
from eqOps import Equals, NotEquals
from proveit.basiclogic.boolean.boolOps import Implies, Not
from proveit.basiclogic.boolean.quantifiers import Forall
from proveit.basiclogic.boolean.boolSet import inBool
from proveit.basiclogic.variables import x, y, z, f
from proveit.basiclogic.simpleExpr import fx, fy

equalityAxioms = Axioms(__package__, locals())

# forall_{x, y} (x=y) in BOOLEANS
equalityInBool = Forall((x, y), inBool(Equals(x, y)))

# forall_{x, y, z} (x=y) => [(y=z) => (x=z)]
equalsTransitivity = Forall((x, y, z), Implies(Equals(x, y), Implies(Equals(y, z), Equals(x, z))))
# forall_{x} x=x
equalsReflexivity = Forall(x, Equals(x, x))
# forall_{x, y} x=y => y=x
equalsSymmetry = Forall((x, y), Implies(Equals(x, y), Equals(y, x)))

# forall_{x, y} [x != y] = Not([x = y])
notEqualsDef = Forall((x, y), Equals(NotEquals(x, y), Not(Equals(x, y))))

# forall_{f, x, y} [(x=y) => f(x)=f(y)]
substitution = Forall((f, x, y), Implies(Equals(x, y), Equals(fx, fy)))

equalityAxioms.finish(locals())
