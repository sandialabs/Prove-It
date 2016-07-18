from proveit.logic import Forall, InSet, Iff, Equals
from proveit.number import Naturals, NaturalsPos
from proveit.number import Add, GreaterThanEquals
from proveit.common import n
from proveit.number.common import zero, one, two
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

naturalsPosDef = Forall(n, Iff(InSet(n, NaturalsPos), GreaterThanEquals(n, one)), domain=Naturals)
naturalsPosDef

zeroInNaturals = InSet(zero,Naturals)
zeroInNaturals

endAxioms(locals(), __package__)
