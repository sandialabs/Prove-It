from proveit import ExpressionList
from proveit.logic import Forall, InSet, Iff, Equals, Implies, SubsetEq, And, SetOfAll, Union
from proveit.number import Naturals, NaturalsPos, Neg, Integers
from proveit.number import Add, GreaterThanEquals
from proveit.number import Len
from proveit.common import n, xMulti, xEtc, x, y, S
from .common import zero, one, two
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

# Define the set of Naturals as, essentially, the minimum set that contains zero and all of its successors;
# that is, n is in Naturals iff n is in all sets that contain zero and all successors.
naturalsDef = Forall(n, Equals(InSet(n, Naturals), Forall(S, Implies(And(InSet(zero, S), Forall(x, InSet(Add(x,one), S), domain=S)), InSet(n, S)))))

# Define the length of an ExpressionList inductively.
exprListLengthDef = And(Equals(Len(), zero), Forall((xMulti, y), Equals(Len(xEtc, y), Add(Len(xEtc), one))))

naturalsPosDef = Forall(n, Iff(InSet(n, NaturalsPos), GreaterThanEquals(n, one)), domain=Naturals)
naturalsPosDef

integersDef = Equals(Integers, Union(Naturals, SetOfAll(n, Neg(n), domain=Naturals)))


endAxioms(locals(), __package__)
