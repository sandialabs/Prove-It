from proveit.logic import Equals
from proveit.number import Mod, ModAbs, Min, Neg
from proveit.common import a, b
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

modAbsDef = Equals(ModAbs(a, b), Min(Mod(a, b), Mod(Neg(a), b)))
modAbsDef

endAxioms(locals(), __package__)


