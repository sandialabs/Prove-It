from proveit import ExpressionList
from proveit.logic import Forall, InSet, Iff, Equals, Implies, SubsetEq, And, SetOfAll, Union
from proveit.number import Naturals, NaturalsPos, Neg, Integers
from proveit.number import Add, GreaterThanEquals
from proveit.common import n, xEtc, x, y, S
from common import zero, one, two
from proveit import beginAxioms, endAxioms

beginAxioms(locals())


naturalsDef = Forall(n, Equals(InSet(n, Naturals), Forall(S, Implies(And(InSet(zero, S), Forall(x, InSet(Add(x,one), S), domain=S)), InSet(n, S)))))

naturalsPosDef = Forall(n, Iff(InSet(n, NaturalsPos), GreaterThanEquals(n, one)), domain=Naturals)
naturalsPosDef

integersDef = Equals(Integers, Union(Naturals, SetOfAll(n, Neg(n), domain=Naturals)))

zeroInNaturals = InSet(zero,Naturals)
zeroInNaturals

endAxioms(locals(), __package__)
