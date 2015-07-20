from proveit.statement import Theorems
from proveit.expression import Literal, Operation, STRING, LATEX
from proveit.multiExpression import Etcetera
from proveit.basiclogic import BOOLEANS, Forall, Exists, And, Or, Implies, Iff, Equals
from setOps import In, NotIn, Singleton, Union, Intersection, SubsetEq, SupersetEq, SetOfAll
from proveit.basiclogic.variables import f, x, y, A, B, C, S, P
from proveit.basiclogic.simpleExpr import fy, Px, Py

setTheorems = Theorems(__package__, locals())

# forall_{A, B} [(A subseteq B) => (forall_{x in A} x in B)]
unfoldSubsetEq = Forall((A, B), Implies(SubsetEq(A, B), Forall(x, In(x, B), In(x, A))))

# forall_{A, B} [(forall_{x in A} x in B) => (A subseteq B)]
foldSubsetEq = Forall((A, B), Implies(Forall(x, In(x, B), In(x, A)), SubsetEq(A, B)))

# forall_{A, B} [A superseteq B => (forall_{x in B} x in A)]
unfoldSupersetEq = Forall((A, B), Implies(SupersetEq(A, B), Forall(x, In(x, A), In(x, B))))

# forall_{A, B} [(forall_{x in B} x in A) => (A superseteq B)]
foldSupersetEq = Forall((A, B), Implies(Forall(x, In(x, A), In(x, B)), SupersetEq(A, B)))

# forall_{P, f, x} [x in {f(y) | P(y)}] => [exists_{y | P(y)} x = f(y)]
unfoldSetOfAll = Forall((P, f, x), Implies(In(x, SetOfAll(y, fy, Py)), Exists(y, Equals(x, fy), Py)))

# forall_{P, f, x} [exists_{y | P(y)} x = f(y)] => [x in {f(y) | P(y)}]
foldSetOfAll = Forall((P, f, x), Implies(Exists(y, Equals(x, fy), Py), In(x, SetOfAll(y, fy, Py))))

# forall_{P, x} [x in {y | P(y)}] => P(x)
unfoldSimpleSetOfAll = Forall((P, x), Implies(In(x, SetOfAll(y, y, Py)), Px))

setTheorems.finish(locals())
